//! Generated functions, module 7 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
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
pub(super) fn case_304_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, a3: Term, a4: Term, a0: Term, v107: Term, v106: Term, v101: Term) -> CheckResult<Option<Term>> {
let v108 = match s.construct(Constructor::eo_extract, &[a3, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v110, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v106, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v101, v113) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v114))
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v95: Term, v97: Term, v96: Term, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
if v95 != v97 { return Ok(None); }
if v96 != a0 { return Ok(None); }
let v98 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_rotate_5fright, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v98, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_extract, &[a2, v103]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v102, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, a3, a4, a0, v107, v106, v101)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v79: Term, a4: Term, a1: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v80 = match s.unapply(v79) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.unapply(v81) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v86 { return Ok(None); }
if v85 != a4 { return Ok(None); }
let v87 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v88, v89)) = v87 else { return Ok(None); }
;
let v90 = match s.unapply(v88) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v91 != v93 { return Ok(None); }
if v92 != a1 { return Ok(None); }
let v94 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v95, v96)) = v94 else { return Ok(None); }
;
let v97 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v95, v97, v96, a0, a1, a2, a3, a4)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v64: Term, a3: Term, v61: Term, a0: Term, a8: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v64 != a3 { return Ok(None); }
let v66 = match s.unapply(v61) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v67, v68)) = v66 else { return Ok(None); }
;
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
let v73 = match s.unapply(v71) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v74 != v76 { return Ok(None); }
if v75 != a0 { return Ok(None); }
let v77 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v68 != v77 { return Ok(None); }
let v78 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v78 else { return Ok(None); }
;
let v79 = fields[0];
more_4_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v79, a4, a1, a0, a2, a3)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v50: Term, a1: Term, v47: Term, a0: Term, v40: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
if v50 != a1 { return Ok(None); }
let v52 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
if v54 != a0 { return Ok(None); }
let v56 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v56 { return Ok(None); }
let v57 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v57 else { return Ok(None); }
;
let v58 = fields[0];
let v59 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
let v62 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v63 != v65 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v64, a3, v61, a0, a8, a4, a1, a2)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s: &mut Store, v32: Term, a2: Term, v33: Term, a1: Term, a0: Term, a7: Term, a3: Term, a8: Term, a4: Term) -> CheckResult<Option<Term>> {
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
if v36 != a2 { return Ok(None); }
let v38 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
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
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v50, a1, v47, a0, v40, a7, a3, a8, a4, a2)
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
let v27 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v27 { return Ok(None); }
let v28 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v28 { return Ok(None); }
let v29 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v29 else { return Ok(None); }
;
let v30 = fields[0];
let v31 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d1(s, v32, a2, v33, a1, a0, a7, a3, a8, a4)
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
pub(super) fn case_305_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2drotate_2dright_2deliminate_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_rotate_5fright, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
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
pub(super) fn case_306_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_307_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_76_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_304_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_305_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_306_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_307_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
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
pub(super) fn case_308_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_309_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a1: Term, v112: Term, v101: Term, v84: Term, v25: Term) -> CheckResult<Option<Term>> {
let v113 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v113, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v112, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v101, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v84, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v25, v118) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v119))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v85: Term, v100: Term, a2: Term, a1: Term, v84: Term, v25: Term) -> CheckResult<Option<Term>> {
let v101 = match s.apply(v85, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v103, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v107]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v108, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v106, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v102, v111) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a1, v112, v101, v84, v25)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v88: Term, a0: Term, v87: Term, v86: Term, v85: Term, a2: Term, a1: Term, v84: Term, v25: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v88, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v87, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v91]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v92, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v90, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v86, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v96, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v85, v100, a2, a1, v84, v25)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v67: Term, v76: Term, a1: Term, v66: Term, v49: Term, v48: Term, a2: Term, a0: Term, v25: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v67, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v78, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v77, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v66, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v49, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v48, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v88, a0, v87, v86, v85, a2, a1, v84, v25)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v64: Term, a0: Term, v50: Term, a2: Term, a1: Term, v49: Term, v48: Term, v25: Term) -> CheckResult<Option<Term>> {
let v65 = match s.apply(v64, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v50, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v68, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v72]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v71, v75) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v67, v76, a1, v66, v49, v48, a2, a0, v25)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a2: Term, a0: Term, v52: Term, v51: Term, v50: Term, a1: Term, v49: Term, v48: Term, v25: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v52, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v56]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v55, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v51, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v61, v63) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v64, a0, v50, a2, a1, v49, v48, v25)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v38: Term, v40: Term, v37: Term, v26: Term, a2: Term, a0: Term, a1: Term, v25: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v43, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v41, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v37, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v26, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a2, a0, v52, v51, v50, a1, v49, v48, v25)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, a2: Term, a0: Term, v28: Term, v27: Term, a1: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v31, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v27, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, v38, v40, v37, v26, a2, a0, a1, v25)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvsdiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsdiv_2deliminate(s, a2, a0, v28, v27, a1, v26, v25)
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
pub(super) fn case_310_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s: &mut Store, v10: Term, v11: Term, v8: Term, v3: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v3, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate(s, v10, v11, v8, v3)
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
pub(super) fn case_311_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_77_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_308_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_309_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_310_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_311_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v18: Term, v62: Term, v17: Term) -> CheckResult<Option<Term>> {
let v63 = match s.apply(v18, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v65, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v63, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v17, v68) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v69))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v49: Term, v50: Term, v47: Term, a0: Term, v46: Term, v45: Term, v32: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v47, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v54, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v52, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24eo_5ftypeof(s, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24eo_5fnil(s, v46, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v45, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v32, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v19, v61) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v18, v62, v17)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v34: Term, v38: Term, a1: Term, v33: Term, a0: Term, v32: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v39 = match s.apply(v34, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v39, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v33, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v49, v50, v47, a0, v46, v45, v32, v19, v18, v17)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, a0: Term, v26: Term, v20: Term, a1: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v26, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v20, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, v34, v38, a1, v33, a0, v32, v19, v18, v17)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s: &mut Store, v14: Term, a0: Term, a1: Term, v13: Term, a2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2duaddo_2deliminate(s, a0, v26, v20, a1, v19, v18, v17)
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
pub(super) fn case_312_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v106: Term, v124: Term, v105: Term, v78: Term, v77: Term, v25: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v106, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v125, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v105, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v78, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v129, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v77, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v25, v132) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v133))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a0: Term, v112: Term, v110: Term, v108: Term, v107: Term, v106: Term, v105: Term, v78: Term, v77: Term, v25: Term) -> CheckResult<Option<Term>> {
let v113 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match eo__24eo_5fnil(s, v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v112, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v110, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v108, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v107, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v121, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v119, v123) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v106, v124, v105, v78, v77, v25)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v91: Term, v100: Term, v90: Term, v79: Term, a2: Term, a0: Term, a1: Term, v78: Term, v77: Term, v25: Term) -> CheckResult<Option<Term>> {
let v101 = match s.apply(v91, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v101, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v90, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v79, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a0, v112, v110, v108, v107, v106, v105, v78, v77, v25)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v84: Term, v88: Term, v80: Term, a2: Term, a1: Term, v79: Term, a0: Term, v78: Term, v77: Term, v25: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v84, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v80, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v96]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v97, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v95, v99) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v91, v100, v90, v79, a2, a0, a1, v78, v77, v25)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v26: Term, v76: Term, a2: Term, a0: Term, a1: Term, v25: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v26, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v82, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v81, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v85]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v86, v87) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v84, v88, v80, a2, a1, v79, a0, v78, v77, v25)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v58: Term, v64: Term, v56: Term, v55: Term, v54: Term, v53: Term, v26: Term, a2: Term, a0: Term, a1: Term, v25: Term) -> CheckResult<Option<Term>> {
let v65 = match s.apply(v58, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v56, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v55, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v69, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v67, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v54, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v53, v75) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v26, v76, a2, a0, a1, v25)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v27: Term, v52: Term, a2: Term, a0: Term, a1: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v27, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match eo__24eo_5fnil(s, v61, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v60, v63) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v58, v64, v56, v55, v54, v53, v26, a2, a0, a1, v25)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a2: Term, a1: Term, v40: Term, v39: Term, v38: Term, v27: Term, a0: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v41 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v43, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v39, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v38, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, v27, v52, a2, a0, a1, v26, v25)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, a2: Term, a0: Term, v28: Term, a1: Term, v27: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v32, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v28, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a2, a1, v40, v39, v38, v27, a0, v26, v25)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvsaddo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsaddo_2deliminate(s, a2, a0, v28, a1, v27, v26, v25)
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
pub(super) fn case_313_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v67: Term, v57: Term, v38: Term) -> CheckResult<Option<Term>> {
let v68 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v57, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v38, v70) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v71))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v41: Term, v55: Term, v39: Term, a1: Term, a2: Term, v38: Term) -> CheckResult<Option<Term>> {
let v56 = match s.apply(v41, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v39, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v61, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v60, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v58, v66) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v67, v57, v38)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v43: Term, v42: Term, a3: Term, v41: Term, v39: Term, a1: Term, a2: Term, v38: Term) -> CheckResult<Option<Term>> {
let v44 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v42, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v48, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v47, v54) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v41, v55, v39, a1, a2, v38)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v31: Term, v33: Term, v32: Term, a1: Term, a0: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v31 != v33 { return Ok(None); }
if v32 != a1 { return Ok(None); }
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_bvsdivo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v34, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v43, v42, a3, v41, v39, a1, a2, v38)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a5: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
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
if v28 != a2 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsdivo_2deliminate(s, v31, v33, v32, a1, a0, a3, a2)
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
pub(super) fn case_314_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_33_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v415: Term, a1: Term, v414: Term, v402: Term, v385: Term, v384: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v416 = match s.apply(v415, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.apply(v414, v416) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.apply(v402, v417) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.apply(v385, v418) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.apply(v384, v419) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.apply(v281, v420) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match s.apply(v174, v421) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.apply(v113, v422) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match s.apply(v38, v423) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v424))
}
pub(super) fn more_32_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v403: Term, v402: Term, v385: Term, v384: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v404 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.apply(v405, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.apply(v404, v406) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v408]) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.apply(v409, v410) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match s.apply(v407, v411) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.apply(v403, v412) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.apply(v413, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_33_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v415, a1, v414, v402, v385, v384, v281, v174, v113, v38)
}
pub(super) fn more_31_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v391: Term, v387: Term, a0: Term, v386: Term, a3: Term, a1: Term, v385: Term, v384: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v392 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v392]) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.apply(v393, v394) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match s.apply(v391, v395) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.apply(v387, v396) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match s.apply(v397, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.apply(v399, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.apply(v398, v400) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.apply(v386, v401) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_32_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v403, v402, v385, v384, v281, v174, v113, v38)
}
pub(super) fn more_30_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v379: Term, v346: Term, v345: Term, v343: Term, v308: Term, a3: Term, a0: Term, a1: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v380 = match eo__24eo_5ftypeof(s, v379) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match eo__24eo_5fnil(s, v346, v380) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.apply(v345, v381) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.apply(v343, v382) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.apply(v308, v383) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match s.apply(v389, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.apply(v388, v390) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v391, v387, a0, v386, a3, a1, v385, v384, v281, v174, v113, v38)
}
pub(super) fn more_29_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v365: Term, v367: Term, v364: Term, a1: Term, v363: Term, v346: Term, v345: Term, v343: Term, v308: Term, a3: Term, a0: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v368 = match s.apply(v365, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v369]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match s.apply(v370, v371) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.apply(v368, v372) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.apply(v364, v373) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.apply(v374, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.apply(v376, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.apply(v375, v377) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.apply(v363, v378) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v379, v346, v345, v343, v308, a3, a0, a1, v281, v174, v113, v38)
}
pub(super) fn more_28_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v354: Term, v355: Term, v352: Term, v348: Term, a0: Term, v347: Term, a3: Term, a1: Term, v346: Term, v345: Term, v343: Term, v308: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v356 = match s.apply(v354, v355) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.apply(v352, v356) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.apply(v348, v357) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.apply(v358, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match s.apply(v360, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.apply(v359, v361) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.apply(v347, v362) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.apply(v366, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v365, v367, v364, a1, v363, v346, v345, v343, v308, a3, a0, v281, v174, v113, v38)
}
pub(super) fn more_27_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a1: Term, a3: Term, a0: Term, v343: Term, v308: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v344 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.apply(v344, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.apply(v350, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.apply(v349, v351) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v353]) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v354, v355, v352, v348, a0, v347, a3, a1, v346, v345, v343, v308, v281, v174, v113, v38)
}
pub(super) fn more_26_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v331: Term, v327: Term, a1: Term, v326: Term, v309: Term, a3: Term, a0: Term, v308: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v332 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v332]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v333, v334) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.apply(v331, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.apply(v327, v336) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v337, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.apply(v339, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v338, v340) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match s.apply(v326, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v309, v342) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a1, a3, a0, v343, v308, v281, v174, v113, v38)
}
pub(super) fn more_25_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v315: Term, v319: Term, v311: Term, a0: Term, v310: Term, a3: Term, a1: Term, v309: Term, v308: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v320 = match s.apply(v315, v319) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v311, v320) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v321, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.apply(v323, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.apply(v322, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.apply(v310, v325) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.apply(v329, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v328, v330) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v331, v327, a1, v326, v309, a3, a0, v308, v281, v174, v113, v38)
}
pub(super) fn more_24_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v282: Term, v307: Term, a3: Term, a0: Term, a1: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v308 = match s.apply(v282, v307) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.apply(v313, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.apply(v312, v314) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v316]) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v317, v318) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v315, v319, v311, a0, v310, a3, a1, v309, v308, v281, v174, v113, v38)
}
pub(super) fn more_23_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v295: Term, v294: Term, v293: Term, v282: Term, a0: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v296 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.apply(v296, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.apply(v295, v297) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v299]) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v300, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match s.apply(v298, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.apply(v294, v303) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v304, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match s.apply(v293, v306) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v282, v307, a3, a0, a1, v281, v174, v113, v38)
}
pub(super) fn more_22_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, v283: Term, a1: Term, v282: Term, v281: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v284 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.apply(v285, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.apply(v284, v286) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v288]) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.apply(v289, v290) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.apply(v287, v291) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.apply(v283, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v295, v294, v293, v282, a0, v281, v174, v113, v38)
}
pub(super) fn more_21_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a1: Term, v271: Term, v259: Term, v242: Term, v241: Term, v240: Term, v238: Term, v201: Term, a3: Term, a0: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v272 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v272, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v271, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.apply(v259, v274) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v242, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match eo__24eo_5ftypeof(s, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match eo__24eo_5fnil(s, v241, v277) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v240, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v238, v279) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match s.apply(v201, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, v283, a1, v282, v281, v174, v113, v38)
}
pub(super) fn more_20_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v259: Term, v242: Term, v241: Term, v240: Term, v238: Term, v201: Term, a0: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v260 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v262, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v261, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v265]) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v266, v267) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v264, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v260, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v270, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a1, v271, v259, v242, v241, v240, v238, v201, a3, a0, v174, v113, v38)
}
pub(super) fn more_19_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v245: Term, v247: Term, v244: Term, a0: Term, v243: Term, a3: Term, a1: Term, v242: Term, v241: Term, v240: Term, v238: Term, v201: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v248 = match s.apply(v245, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v249]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v250, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v248, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v244, v253) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v254, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v256, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v255, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v243, v258) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v259, v242, v241, v240, v238, v201, a0, v174, v113, v38)
}
pub(super) fn more_18_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v220: Term, v235: Term, v203: Term, v202: Term, a1: Term, a3: Term, a0: Term, v201: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v236 = match s.apply(v220, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.apply(v203, v236) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.apply(v202, v237) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.apply(v239, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v246, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v245, v247, v244, a0, v243, a3, a1, v242, v241, v240, v238, v201, v174, v113, v38)
}
pub(super) fn more_17_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v223: Term, a1: Term, v222: Term, v221: Term, v220: Term, v203: Term, v202: Term, a3: Term, a0: Term, v201: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v224 = match s.apply(v223, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v222, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v226]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v227, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v225, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v221, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v231, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v233, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.apply(v232, v234) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v220, v235, v203, v202, a1, a3, a0, v201, v174, v113, v38)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v211: Term, v209: Term, v205: Term, a0: Term, v204: Term, a3: Term, a1: Term, v203: Term, v202: Term, v201: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v212 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v211, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v209, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.apply(v205, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v215, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v217, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.apply(v216, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v204, v219) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v223, a1, v222, v221, v220, v203, v202, a3, a0, v201, v174, v113, v38)
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v186: Term, v199: Term, v175: Term, a3: Term, a0: Term, a1: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v200 = match s.apply(v186, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v175, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.apply(v207, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.apply(v206, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v210]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v211, v209, v205, a0, v204, a3, a1, v203, v202, v201, v174, v113, v38)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v187: Term, v186: Term, v175: Term, a0: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v188 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v189, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v188, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v192]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v193, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v191, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.apply(v187, v196) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v197, v198) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v186, v199, v175, a3, a0, a1, v174, v113, v38)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, a1: Term, v175: Term, v174: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v176 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v178, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v177, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v181]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v182, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v180, v184) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v176, v185) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v187, v186, v175, a0, v174, v113, v38)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v163: Term, v162: Term, v158: Term, a1: Term, v157: Term, v140: Term, a3: Term, a0: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v164 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v163]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v164, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v162, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v158, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v169, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v157, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v140, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, a1, v175, v174, v113, v38)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v142: Term, v151: Term, a0: Term, v141: Term, a3: Term, a1: Term, v140: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v152 = match s.apply(v142, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v152, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v154, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v153, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v141, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v159, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v163, v162, v158, a1, v157, v140, a3, a0, v113, v38)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v114: Term, v139: Term, a3: Term, a0: Term, a1: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v140 = match s.apply(v114, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v144, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v143, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v148, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v146, v150) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v142, v151, a0, v141, a3, a1, v140, v113, v38)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a1: Term, v127: Term, v126: Term, v125: Term, v114: Term, a0: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v128 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v127, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v131]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v132, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v130, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v126, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v136, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v125, v138) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v114, v139, a3, a0, a1, v113, v38)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, v115: Term, a1: Term, v114: Term, v113: Term, v38: Term) -> CheckResult<Option<Term>> {
let v116 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v116, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v120]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v121, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v119, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v115, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a1, v127, v126, v125, v114, a0, v113, v38)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v103: Term, v101: Term, v97: Term, a1: Term, v96: Term, v79: Term, a3: Term, a0: Term, v38: Term) -> CheckResult<Option<Term>> {
let v104 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v103, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v101, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v97, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v108, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v96, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v79, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, v115, a1, v114, v113, v38)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v91: Term, a0: Term, v80: Term, a3: Term, a1: Term, v79: Term, v38: Term) -> CheckResult<Option<Term>> {
let v92 = match s.apply(v91, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v80, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v98, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v102]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v103, v101, v97, a1, v96, v79, a3, a0, v38)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, a1: Term, v79: Term, v38: Term) -> CheckResult<Option<Term>> {
let v80 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v82, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v86]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v87, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v85, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v81, v90) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v91, a0, v80, a3, a1, v79, v38)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v58: Term, v67: Term, a1: Term, v57: Term, v40: Term, a2: Term, v39: Term, a3: Term, a0: Term, v38: Term) -> CheckResult<Option<Term>> {
let v68 = match s.apply(v58, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v69, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v57, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v40, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v75, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v74, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v39, v78) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, a1, v79, v38)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v53: Term, v55: Term, v41: Term, a3: Term, a1: Term, v40: Term, a2: Term, v39: Term, a0: Term, v38: Term) -> CheckResult<Option<Term>> {
let v56 = match s.apply(v53, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v41, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v63]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v64, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v62, v66) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v58, v67, a1, v57, v40, a2, v39, a3, a0, v38)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, a3: Term, a0: Term, v43: Term, v42: Term, v41: Term, a1: Term, v40: Term, a2: Term, v39: Term, v38: Term) -> CheckResult<Option<Term>> {
let v44 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v47]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v48, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v46, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v42, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, v53, v55, v41, a3, a1, v40, a2, v39, a0, v38)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s: &mut Store, v24: Term, a0: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
let v33 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v33 { return Ok(None); }
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_bvsmod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v34, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsmod_2deliminate(s, a3, a0, v43, v42, v41, a1, v40, a2, v39, v38)
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
pub(super) fn case_315_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_78_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_312_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_313_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_314_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_315_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, a1: Term, v100: Term, v89: Term, v72: Term, v25: Term) -> CheckResult<Option<Term>> {
let v101 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v100, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v103, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v89, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v72, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v25, v106) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v107))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v73: Term, v88: Term, a2: Term, a1: Term, v72: Term, v25: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v73, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v91, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v95]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v94, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v90, v99) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, a1, v100, v89, v72, v25)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v76: Term, a0: Term, v75: Term, v74: Term, v73: Term, a2: Term, a1: Term, v72: Term, v25: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v76, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v79]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v78, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v74, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v85, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v84, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v73, v88, a2, a1, v72, v25)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v55: Term, v64: Term, a1: Term, v54: Term, v37: Term, v36: Term, a2: Term, a0: Term, v25: Term) -> CheckResult<Option<Term>> {
let v65 = match s.apply(v55, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v65, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v54, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v37, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v36, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v76, a0, v75, v74, v73, a2, a1, v72, v25)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v52: Term, a0: Term, v38: Term, a2: Term, a1: Term, v37: Term, v36: Term, v25: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v52, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v38, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v60]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v61, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v59, v63) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v55, v64, a1, v54, v37, v36, a2, a0, v25)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, a2: Term, a0: Term, v40: Term, v39: Term, v38: Term, a1: Term, v37: Term, v36: Term, v25: Term) -> CheckResult<Option<Term>> {
let v41 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v43, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v39, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v52, a0, v38, a2, a1, v37, v36, v25)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v28: Term, a0: Term, v27: Term, v26: Term, a2: Term, a1: Term, v25: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v30, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v26, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, a2, a0, v40, v39, v38, a1, v37, v36, v25)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvsrem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsrem_2deliminate(s, v28, a0, v27, v26, a2, a1, v25)
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
pub(super) fn case_316_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s: &mut Store, v26: Term, a1: Term, v24: Term, v19: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v19, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v18, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v30, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v17, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v36))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s: &mut Store, v14: Term, a0: Term, a1: Term, v13: Term, a2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_zero_5fextend, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_zero_5fextend, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dusubo_2deliminate(s, v26, a1, v24, v19, v18, v17)
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
pub(super) fn case_317_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v100: Term, v112: Term, v99: Term, v72: Term, v71: Term, v25: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v100, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v113, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v99, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v72, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v117, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v71, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v25, v120) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v121))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a2: Term, a0: Term, a1: Term, v100: Term, v99: Term, v72: Term, v71: Term, v25: Term) -> CheckResult<Option<Term>> {
let v101 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v103, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v102, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v101, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v108]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v109, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v107, v111) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v100, v112, v99, v72, v71, v25)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v86: Term, v88: Term, v85: Term, v84: Term, v73: Term, a2: Term, a0: Term, a1: Term, v72: Term, v71: Term, v25: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v86, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v90]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v91, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v89, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v85, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v95, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v84, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v73, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a2, a0, a1, v100, v99, v72, v71, v25)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v76: Term, a0: Term, v75: Term, v74: Term, a2: Term, a1: Term, v73: Term, v72: Term, v71: Term, v25: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v76, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v79]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v78, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v74, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v86, v88, v85, v84, v73, a2, a0, a1, v72, v71, v25)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v63: Term, v64: Term, v61: Term, v54: Term, v53: Term, v26: Term, a2: Term, a0: Term, a1: Term, v25: Term) -> CheckResult<Option<Term>> {
let v65 = match s.apply(v63, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v61, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v54, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v53, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v26, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v76, a0, v75, v74, a2, a1, v73, v72, v71, v25)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v27: Term, v52: Term, a2: Term, a0: Term, a1: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v27, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v56, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v55, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v62]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v63, v64, v61, v54, v53, v26, a2, a0, a1, v25)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a2: Term, a1: Term, v40: Term, v39: Term, v38: Term, v27: Term, a0: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v41 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v45, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v43, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v39, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v38, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, v27, v52, a2, a0, a1, v26, v25)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, a2: Term, a0: Term, v28: Term, a1: Term, v27: Term, v26: Term, v25: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_extract, &[a2, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v32, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v28, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a2, a1, v40, v39, v38, v27, a0, v26, v25)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvssubo, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dssubo_2deliminate(s, a2, a0, v28, a1, v27, v26, v25)
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
pub(super) fn case_318_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, v26: Term, v40: Term, v24: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v26, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v24, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v42))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, v28: Term, v27: Term, a1: Term, v26: Term, v24: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v27, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v33, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v37, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v32, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, v26, v40, v24)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvnego, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dnego_2deliminate(s, v28, v27, a1, v26, v24)
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
pub(super) fn case_319_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_320_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-const-cond-1"
pub fn eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1(s, a0, a1);
s.leave();
result
}
pub(super) fn case_321_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d1(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-const-cond-2"
pub fn eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2(s, a0, a1);
s.leave();
result
}
pub(super) fn case_322_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fconst_5fcond_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dite_2dconst_2dcond_2d2(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s: &mut Store, v7: Term, v11: Term, v0: Term, a0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d1(s, v7, v11, v0, a0)
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
pub(super) fn case_323_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_80_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_320_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_321_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_322_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_323_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s: &mut Store, v7: Term, v11: Term, v0: Term, a0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dconst_2dchildren_2d2(s, v7, v11, v0, a0)
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
pub(super) fn case_324_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_325_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_326_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_327_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_81_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_324_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_325_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_326_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_327_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2dif(s: &mut Store, v11: Term, a0: Term, a1: Term, v10: Term, a3: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v10, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v9, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
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
pub(super) fn case_328_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v10, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v9, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
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
pub(super) fn case_329_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, v23: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v23, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v9, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s: &mut Store, a0: Term, v11: Term, a1: Term, v10: Term, a3: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v10, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a3) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dite_2dmerge_2dthen_2delse(s, v23, a2, v9)
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
pub(super) fn case_330_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v17 = match s.literal(Lit::Binary(BitVec::new(1, &Integer::from(1u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v10, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v9, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
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
pub(super) fn case_331_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_82_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_328_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_329_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_330_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_331_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d0(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
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
pub(super) fn case_332_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v73: Term, v68: Term, v63: Term) -> CheckResult<Option<Term>> {
let v74 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v68, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v63, v76) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v77))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v59: Term, v61: Term, v57: Term, a3: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v57, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_extract, &[a3, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v64, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v70, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v69, v72) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v73, v68, v63)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s: &mut Store, v43: Term, a1: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v49 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
if v54 != a1 { return Ok(None); }
let v56 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v56 { return Ok(None); }
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dshl_2dby_2dconst_2d1(s, v59, v61, v57, a3, a0, a1)
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
let v48 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
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
pub(super) fn case_333_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v67 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v66, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v65, v68) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v69))
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
pub(super) fn case_334_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
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
pub(super) fn case_335_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v57: Term, v53: Term, v48: Term) -> CheckResult<Option<Term>> {
let v58 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v53, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v48, v60) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v61))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s: &mut Store, v45: Term, a1: Term, v44: Term, v42: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v46 = match s.apply(v45, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v42, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v50, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v49, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_extract, &[a3, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v54, v56) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v57, v53, v48)
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
let v41 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v41 { return Ok(None); }
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_bvlshr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dlshr_2dby_2dconst_2d1(s, v45, a1, v44, v42, a3, a0)
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
pub(super) fn case_336_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v54 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v53, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v52, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v56))
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
pub(super) fn case_337_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
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
pub(super) fn case_338_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v55: Term, v57: Term, v54: Term, v48: Term) -> CheckResult<Option<Term>> {
let v58 = match s.apply(v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v58, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v54, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v48, v61) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v62))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s: &mut Store, v45: Term, a1: Term, v44: Term, v42: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v46 = match s.apply(v45, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v42, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_repeat, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v50, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v49, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_extract, &[a3, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v55, v57, v54, v48)
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
let v41 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v41 { return Ok(None); }
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d1(s, v45, a1, v44, v42, a3, a0)
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
pub(super) fn case_339_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_84_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_336_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_337_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_338_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_339_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v86: Term, v90: Term) -> CheckResult<Option<Term>> {
let v91 = match s.apply(v86, v90) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v91))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v78: Term, a0: Term, a2: Term, a1: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
if v78 != a0 { return Ok(None); }
let v80 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v82, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v80, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_repeat, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_extract, &[a3, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v87, v89) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v86, v90)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s: &mut Store, v64: Term, a0: Term, v57: Term, a8: Term, a4: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v64 != a0 { return Ok(None); }
let v66 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v66 { return Ok(None); }
let v67 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v67 else { return Ok(None); }
;
let v68 = fields[0];
let v69 = match s.unapply(v68) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.unapply(v70) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
let v75 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v75 { return Ok(None); }
if v74 != a4 { return Ok(None); }
let v76 = match s.unapply(v71) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v77 != v79 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dashr_2dby_2dconst_2d2(s, v78, a0, a2, a1, a4, a3)
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
pub(super) fn case_340_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v128: Term, v136: Term, v127: Term, v125: Term, v116: Term, v115: Term, v84: Term) -> CheckResult<Option<Term>> {
let v137 = match eo__24eo_5fnil(s, v128, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v127, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v125, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v116, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v140, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v115, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v84, v143) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v144))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v117: Term, v124: Term, a2: Term, a7: Term, a0: Term, a1: Term, v116: Term, v115: Term, v84: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v117, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_extract, &[a7, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_list(EvalOp::ListConcat, &[v132, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.builtin_list(EvalOp::ListSingletonElim, &[v131, v133]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v130, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24eo_5ftypeof(s, v135) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v128, v136, v127, v125, v116, v115, v84)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v103: Term, v112: Term, v93: Term, v85: Term, a7: Term, a0: Term, a1: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v103, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v93, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v85, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_extract, &[a7, v118]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_list(EvalOp::ListConcat, &[v121, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_list(EvalOp::ListSingletonElim, &[v120, v122]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v119, v123) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v117, v124, a2, a7, a0, a1, v116, v115, v84)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v96: Term, a4: Term, v100: Term, v95: Term, v94: Term, a5: Term, a6: Term, a0: Term, a1: Term, v93: Term, v85: Term, a7: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v101 = match s.builtin_list(EvalOp::ListConcat, &[v96, a4, v100]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_list(EvalOp::ListSingletonElim, &[v95, v101]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v94, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_list(EvalOp::ListConcat, &[v107, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.builtin_list(EvalOp::ListSingletonElim, &[v106, v108]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v105, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24eo_5ftypeof(s, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24eo_5fnil(s, v104, v111) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v103, v112, v93, v85, a7, a0, a1, a2, v84)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v88: Term, v87: Term, v86: Term, a3: Term, a4: Term, a5: Term, a6: Term, v85: Term, a7: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v89 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_list(EvalOp::ListConcat, &[v89, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.builtin_list(EvalOp::ListSingletonElim, &[v88, v90]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v87, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v86, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v98, v99) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v96, a4, v100, v95, v94, a5, a6, a0, a1, v93, v85, a7, a2, v84)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v76: Term, v74: Term, v72: Term, a4: Term, v71: Term, a1: Term, v70: Term, a0: Term, v69: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term) -> CheckResult<Option<Term>> {
let v77 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v76, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.builtin_list(EvalOp::ListConcat, &[v72, a4, v79]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v71, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListConcat, &[v70, a0, v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v69, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, a0, a1, v88, v87, v86, a3, a4, a5, a6, v85, a7, a2, v84)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, v65: Term, v67: Term, v66: Term, a2: Term, v59: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v65 != v67 { return Ok(None); }
if v66 != a2 { return Ok(None); }
let v68 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v68 { return Ok(None); }
let v69 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v76, v74, v72, a4, v71, a1, v70, a0, v69, a5, a6, a3, a7, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s: &mut Store, a10: Term, a7: Term, a2: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v48 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v48 else { return Ok(None); }
;
let v49 = fields[0];
let v50 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
if v55 != a7 { return Ok(None); }
let v57 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v61 != v63 { return Ok(None); }
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
let v67 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup(s, v65, v67, v66, a2, v59, a3, a4, a1, a0, a5, a6, a7)
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
let v47 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v47 { return Ok(None); }
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
pub(super) fn case_341_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v128: Term, v136: Term, v127: Term, v125: Term, v116: Term, v115: Term, v84: Term) -> CheckResult<Option<Term>> {
let v137 = match eo__24eo_5fnil(s, v128, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v127, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v125, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v116, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v140, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v115, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v84, v143) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v144))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v117: Term, v124: Term, a2: Term, a7: Term, a0: Term, a1: Term, v116: Term, v115: Term, v84: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v117, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_extract, &[a7, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_list(EvalOp::ListConcat, &[v132, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.builtin_list(EvalOp::ListSingletonElim, &[v131, v133]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v130, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24eo_5ftypeof(s, v135) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v128, v136, v127, v125, v116, v115, v84)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v103: Term, v112: Term, v93: Term, v85: Term, a7: Term, a0: Term, a1: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v103, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v93, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v85, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_extract, &[a7, v118]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_list(EvalOp::ListConcat, &[v121, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_list(EvalOp::ListSingletonElim, &[v120, v122]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v119, v123) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v117, v124, a2, a7, a0, a1, v116, v115, v84)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v96: Term, a4: Term, v100: Term, v95: Term, v94: Term, a5: Term, a6: Term, a0: Term, a1: Term, v93: Term, v85: Term, a7: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v101 = match s.builtin_list(EvalOp::ListConcat, &[v96, a4, v100]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_list(EvalOp::ListSingletonElim, &[v95, v101]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v94, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_list(EvalOp::ListConcat, &[v107, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.builtin_list(EvalOp::ListSingletonElim, &[v106, v108]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v105, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24eo_5ftypeof(s, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24eo_5fnil(s, v104, v111) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v103, v112, v93, v85, a7, a0, a1, a2, v84)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v88: Term, v87: Term, v86: Term, a3: Term, a4: Term, a5: Term, a6: Term, v85: Term, a7: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v89 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_list(EvalOp::ListConcat, &[v89, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.builtin_list(EvalOp::ListSingletonElim, &[v88, v90]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v87, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v86, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v98, v99) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v96, a4, v100, v95, v94, a5, a6, a0, a1, v93, v85, a7, a2, v84)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v76: Term, v74: Term, v72: Term, a4: Term, v71: Term, a1: Term, v70: Term, a0: Term, v69: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term) -> CheckResult<Option<Term>> {
let v77 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v76, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.builtin_list(EvalOp::ListConcat, &[v72, a4, v79]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v71, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListConcat, &[v70, a0, v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v69, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, a0, a1, v88, v87, v86, a3, a4, a5, a6, v85, a7, a2, v84)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, v65: Term, v67: Term, v66: Term, a2: Term, v59: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v65 != v67 { return Ok(None); }
if v66 != a2 { return Ok(None); }
let v68 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v68 { return Ok(None); }
let v69 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v76, v74, v72, a4, v71, a1, v70, a0, v69, a5, a6, a3, a7, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s: &mut Store, a10: Term, a7: Term, a2: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v48 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v48 else { return Ok(None); }
;
let v49 = fields[0];
let v50 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
if v55 != a7 { return Ok(None); }
let v57 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v61 != v63 { return Ok(None); }
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
let v67 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup(s, v65, v67, v66, a2, v59, a3, a4, a1, a0, a5, a6, a7)
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
let v47 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v47 { return Ok(None); }
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
pub(super) fn case_342_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v128: Term, v136: Term, v127: Term, v125: Term, v116: Term, v115: Term, v84: Term) -> CheckResult<Option<Term>> {
let v137 = match eo__24eo_5fnil(s, v128, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v127, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v125, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v116, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v140, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v115, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v84, v143) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v144))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v117: Term, v124: Term, a2: Term, a7: Term, a0: Term, a1: Term, v116: Term, v115: Term, v84: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v117, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_extract, &[a7, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_list(EvalOp::ListConcat, &[v132, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.builtin_list(EvalOp::ListSingletonElim, &[v131, v133]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v130, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24eo_5ftypeof(s, v135) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v128, v136, v127, v125, v116, v115, v84)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v103: Term, v112: Term, v93: Term, v85: Term, a7: Term, a0: Term, a1: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v113 = match s.apply(v103, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v93, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v85, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_extract, &[a7, v118]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_list(EvalOp::ListConcat, &[v121, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.builtin_list(EvalOp::ListSingletonElim, &[v120, v122]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v119, v123) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v117, v124, a2, a7, a0, a1, v116, v115, v84)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v96: Term, a4: Term, v100: Term, v95: Term, v94: Term, a5: Term, a6: Term, a0: Term, a1: Term, v93: Term, v85: Term, a7: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v101 = match s.builtin_list(EvalOp::ListConcat, &[v96, a4, v100]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.builtin_list(EvalOp::ListSingletonElim, &[v95, v101]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v94, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.builtin_list(EvalOp::ListConcat, &[v107, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.builtin_list(EvalOp::ListSingletonElim, &[v106, v108]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v105, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24eo_5ftypeof(s, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match eo__24eo_5fnil(s, v104, v111) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v103, v112, v93, v85, a7, a0, a1, a2, v84)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a0: Term, a1: Term, v88: Term, v87: Term, v86: Term, a3: Term, a4: Term, a5: Term, a6: Term, v85: Term, a7: Term, a2: Term, v84: Term) -> CheckResult<Option<Term>> {
let v89 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_list(EvalOp::ListConcat, &[v89, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.builtin_list(EvalOp::ListSingletonElim, &[v88, v90]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v87, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v86, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v97, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v98, v99) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v96, a4, v100, v95, v94, a5, a6, a0, a1, v93, v85, a7, a2, v84)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v76: Term, v74: Term, v72: Term, a4: Term, v71: Term, a1: Term, v70: Term, a0: Term, v69: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term) -> CheckResult<Option<Term>> {
let v77 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v76, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.builtin_list(EvalOp::ListConcat, &[v72, a4, v79]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v71, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListConcat, &[v70, a0, v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v69, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, a0, a1, v88, v87, v86, a3, a4, a5, a6, v85, a7, a2, v84)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, v65: Term, v67: Term, v66: Term, a2: Term, v59: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v65 != v67 { return Ok(None); }
if v66 != a2 { return Ok(None); }
let v68 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v68 { return Ok(None); }
let v69 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v76, v74, v72, a4, v71, a1, v70, a0, v69, a5, a6, a3, a7, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s: &mut Store, a10: Term, a7: Term, a2: Term, a3: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v48 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v48 else { return Ok(None); }
;
let v49 = fields[0];
let v50 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
if v55 != a7 { return Ok(None); }
let v57 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v61 != v63 { return Ok(None); }
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
let v67 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup(s, v65, v67, v66, a2, v59, a3, a4, a1, a0, a5, a6, a7)
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
let v47 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v47 { return Ok(None); }
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
pub(super) fn case_343_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_85_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_340_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_341_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_342_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_343_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v154: Term, v186: Term, v131: Term) -> CheckResult<Option<Term>> {
let v187 = match s.apply(v154, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v131, v187) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v188))
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v174: Term, v172: Term, v171: Term, v164: Term, v155: Term, v154: Term, v131: Term) -> CheckResult<Option<Term>> {
let v175 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListConcat, &[v176, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.builtin_list(EvalOp::ListSingletonElim, &[v175, v177]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v174, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match eo__24eo_5ftypeof(s, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match eo__24eo_5fnil(s, v172, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v171, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v164, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v155, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v184, v185) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v154, v186, v131)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v158: Term, v162: Term, v156: Term, a2: Term, a4: Term, a7: Term, a0: Term, a1: Term, v155: Term, v154: Term, v131: Term) -> CheckResult<Option<Term>> {
let v163 = match s.apply(v158, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v156, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v167, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.builtin_list(EvalOp::ListSingletonElim, &[v166, v169]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v165, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_extract, &[a7, v173]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, a0, a1, v174, v172, v171, v164, v155, v154, v131)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v143: Term, v150: Term, v142: Term, v140: Term, v132: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v131: Term) -> CheckResult<Option<Term>> {
let v151 = match eo__24eo_5fnil(s, v143, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v142, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v140, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v132, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_extract, &[a7, v157]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_list(EvalOp::ListConcat, &[v160, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListSingletonElim, &[v159, v161]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v158, v162, v156, a2, a4, a7, a0, a1, v155, v154, v131)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v134: Term, v138: Term, v133: Term, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v132: Term, a7: Term, a2: Term, a4: Term, v131: Term) -> CheckResult<Option<Term>> {
let v139 = match s.apply(v134, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v133, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_list(EvalOp::ListConcat, &[v146, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_list(EvalOp::ListSingletonElim, &[v145, v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v144, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match eo__24eo_5ftypeof(s, v149) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v143, v150, v142, v140, v132, a7, a0, a1, a2, a4, v131)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v123: Term, v126: Term, v121: Term, a1: Term, v120: Term, a0: Term, v119: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v127 = match s.apply(v123, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v121, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_list(EvalOp::ListConcat, &[v120, a0, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v119, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_list(EvalOp::ListConcat, &[v136, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.builtin_list(EvalOp::ListSingletonElim, &[v135, v137]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v134, v138, v133, a3, a5, a6, a0, a1, v132, a7, a2, a4, v131)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v115: Term, v117: Term, v116: Term, a3: Term, v84: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v115 != v117 { return Ok(None); }
if v116 != a3 { return Ok(None); }
let v118 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v118 { return Ok(None); }
let v119 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v125, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v123, v126, v121, a1, v120, a0, v119, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v101: Term, a3: Term, v102: Term, a2: Term, a4: Term, v91: Term, v84: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v103 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v104, v105)) = v103 else { return Ok(None); }
;
let v106 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v104 != v106 { return Ok(None); }
if v105 != a3 { return Ok(None); }
let v107 = match s.unapply(v102) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v108, v109)) = v107 else { return Ok(None); }
;
let v110 = match s.unapply(v108) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v111 != v113 { return Ok(None); }
if v112 != a2 { return Ok(None); }
if v109 != a4 { return Ok(None); }
let v114 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v115, v116)) = v114 else { return Ok(None); }
;
let v117 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v115, v117, v116, a3, v84, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v77: Term, a3: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v82 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v83, v84)) = v82 else { return Ok(None); }
;
let v85 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v86 != v88 { return Ok(None); }
let v89 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v90, v91)) = v89 else { return Ok(None); }
;
let v92 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v93 != v95 { return Ok(None); }
let v96 = match s.unapply(v94) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v97, v98)) = v96 else { return Ok(None); }
;
let v99 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v97 != v99 { return Ok(None); }
let v100 = match s.unapply(v98) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v101, v102)) = v100 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v101, a3, v102, a2, a4, v91, v84, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v71 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a2 { return Ok(None); }
if v67 != a4 { return Ok(None); }
let v72 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v72 { return Ok(None); }
let v73 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v73 else { return Ok(None); }
;
let v74 = fields[0];
let v75 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v76, v77)) = v75 else { return Ok(None); }
;
let v78 = match s.unapply(v76) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v79 != v81 { return Ok(None); }
if v80 != a7 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup2(s, v77, a3, a2, a4, a1, a0, a5, a6, a7)
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
pub(super) fn case_344_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v154: Term, v186: Term, v131: Term) -> CheckResult<Option<Term>> {
let v187 = match s.apply(v154, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v131, v187) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v188))
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v174: Term, v172: Term, v171: Term, v164: Term, v155: Term, v154: Term, v131: Term) -> CheckResult<Option<Term>> {
let v175 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListConcat, &[v176, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.builtin_list(EvalOp::ListSingletonElim, &[v175, v177]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v174, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match eo__24eo_5ftypeof(s, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match eo__24eo_5fnil(s, v172, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v171, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v164, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v155, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v184, v185) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v154, v186, v131)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v158: Term, v162: Term, v156: Term, a2: Term, a4: Term, a7: Term, a0: Term, a1: Term, v155: Term, v154: Term, v131: Term) -> CheckResult<Option<Term>> {
let v163 = match s.apply(v158, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v156, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v167, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.builtin_list(EvalOp::ListSingletonElim, &[v166, v169]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v165, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_extract, &[a7, v173]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, a0, a1, v174, v172, v171, v164, v155, v154, v131)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v143: Term, v150: Term, v142: Term, v140: Term, v132: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v131: Term) -> CheckResult<Option<Term>> {
let v151 = match eo__24eo_5fnil(s, v143, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v142, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v140, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v132, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_extract, &[a7, v157]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_list(EvalOp::ListConcat, &[v160, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListSingletonElim, &[v159, v161]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v158, v162, v156, a2, a4, a7, a0, a1, v155, v154, v131)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v134: Term, v138: Term, v133: Term, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v132: Term, a7: Term, a2: Term, a4: Term, v131: Term) -> CheckResult<Option<Term>> {
let v139 = match s.apply(v134, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v133, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_list(EvalOp::ListConcat, &[v146, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_list(EvalOp::ListSingletonElim, &[v145, v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v144, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match eo__24eo_5ftypeof(s, v149) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v143, v150, v142, v140, v132, a7, a0, a1, a2, a4, v131)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v123: Term, v126: Term, v121: Term, a1: Term, v120: Term, a0: Term, v119: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v127 = match s.apply(v123, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v121, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_list(EvalOp::ListConcat, &[v120, a0, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v119, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_list(EvalOp::ListConcat, &[v136, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.builtin_list(EvalOp::ListSingletonElim, &[v135, v137]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v134, v138, v133, a3, a5, a6, a0, a1, v132, a7, a2, a4, v131)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v115: Term, v117: Term, v116: Term, a3: Term, v84: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v115 != v117 { return Ok(None); }
if v116 != a3 { return Ok(None); }
let v118 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v118 { return Ok(None); }
let v119 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v125, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v123, v126, v121, a1, v120, a0, v119, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v101: Term, a3: Term, v102: Term, a2: Term, a4: Term, v91: Term, v84: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v103 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v104, v105)) = v103 else { return Ok(None); }
;
let v106 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v104 != v106 { return Ok(None); }
if v105 != a3 { return Ok(None); }
let v107 = match s.unapply(v102) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v108, v109)) = v107 else { return Ok(None); }
;
let v110 = match s.unapply(v108) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v111 != v113 { return Ok(None); }
if v112 != a2 { return Ok(None); }
if v109 != a4 { return Ok(None); }
let v114 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v115, v116)) = v114 else { return Ok(None); }
;
let v117 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v115, v117, v116, a3, v84, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v77: Term, a3: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v82 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v83, v84)) = v82 else { return Ok(None); }
;
let v85 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v86 != v88 { return Ok(None); }
let v89 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v90, v91)) = v89 else { return Ok(None); }
;
let v92 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v93 != v95 { return Ok(None); }
let v96 = match s.unapply(v94) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v97, v98)) = v96 else { return Ok(None); }
;
let v99 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v97 != v99 { return Ok(None); }
let v100 = match s.unapply(v98) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v101, v102)) = v100 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v101, a3, v102, a2, a4, v91, v84, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v71 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a2 { return Ok(None); }
if v67 != a4 { return Ok(None); }
let v72 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v72 { return Ok(None); }
let v73 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v73 else { return Ok(None); }
;
let v74 = fields[0];
let v75 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v76, v77)) = v75 else { return Ok(None); }
;
let v78 = match s.unapply(v76) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v79 != v81 { return Ok(None); }
if v80 != a7 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup2(s, v77, a3, a2, a4, a1, a0, a5, a6, a7)
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
pub(super) fn case_345_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v154: Term, v186: Term, v131: Term) -> CheckResult<Option<Term>> {
let v187 = match s.apply(v154, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v131, v187) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v188))
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, a0: Term, a1: Term, v174: Term, v172: Term, v171: Term, v164: Term, v155: Term, v154: Term, v131: Term) -> CheckResult<Option<Term>> {
let v175 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListConcat, &[v176, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.builtin_list(EvalOp::ListSingletonElim, &[v175, v177]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v174, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match eo__24eo_5ftypeof(s, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match eo__24eo_5fnil(s, v172, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v171, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v164, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v155, v183) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v184, v185) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v154, v186, v131)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v158: Term, v162: Term, v156: Term, a2: Term, a4: Term, a7: Term, a0: Term, a1: Term, v155: Term, v154: Term, v131: Term) -> CheckResult<Option<Term>> {
let v163 = match s.apply(v158, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v156, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v167, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.builtin_list(EvalOp::ListSingletonElim, &[v166, v169]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v165, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_extract, &[a7, v173]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, a0, a1, v174, v172, v171, v164, v155, v154, v131)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v143: Term, v150: Term, v142: Term, v140: Term, v132: Term, a7: Term, a0: Term, a1: Term, a2: Term, a4: Term, v131: Term) -> CheckResult<Option<Term>> {
let v151 = match eo__24eo_5fnil(s, v143, v150) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v142, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v140, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v132, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_extract, &[a7, v157]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_list(EvalOp::ListConcat, &[v160, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListSingletonElim, &[v159, v161]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v158, v162, v156, a2, a4, a7, a0, a1, v155, v154, v131)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v134: Term, v138: Term, v133: Term, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v132: Term, a7: Term, a2: Term, a4: Term, v131: Term) -> CheckResult<Option<Term>> {
let v139 = match s.apply(v134, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v133, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.builtin_list(EvalOp::ListConcat, &[v146, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_list(EvalOp::ListSingletonElim, &[v145, v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v144, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match eo__24eo_5ftypeof(s, v149) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v143, v150, v142, v140, v132, a7, a0, a1, a2, a4, v131)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v123: Term, v126: Term, v121: Term, a1: Term, v120: Term, a0: Term, v119: Term, a5: Term, a6: Term, a3: Term, a7: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v127 = match s.apply(v123, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v121, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.builtin_list(EvalOp::ListConcat, &[v120, a0, v129]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v119, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_list(EvalOp::ListConcat, &[v136, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.builtin_list(EvalOp::ListSingletonElim, &[v135, v137]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v134, v138, v133, a3, a5, a6, a0, a1, v132, a7, a2, a4, v131)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v115: Term, v117: Term, v116: Term, a3: Term, v84: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v115 != v117 { return Ok(None); }
if v116 != a3 { return Ok(None); }
let v118 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v118 { return Ok(None); }
let v119 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v125, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v123, v126, v121, a1, v120, a0, v119, a5, a6, a3, a7, a2, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v101: Term, a3: Term, v102: Term, a2: Term, a4: Term, v91: Term, v84: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v103 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v104, v105)) = v103 else { return Ok(None); }
;
let v106 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v104 != v106 { return Ok(None); }
if v105 != a3 { return Ok(None); }
let v107 = match s.unapply(v102) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v108, v109)) = v107 else { return Ok(None); }
;
let v110 = match s.unapply(v108) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v111 != v113 { return Ok(None); }
if v112 != a2 { return Ok(None); }
if v109 != a4 { return Ok(None); }
let v114 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v115, v116)) = v114 else { return Ok(None); }
;
let v117 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v115, v117, v116, a3, v84, a2, a4, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v77: Term, a3: Term, a2: Term, a4: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v82 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v83, v84)) = v82 else { return Ok(None); }
;
let v85 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v86 != v88 { return Ok(None); }
let v89 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v90, v91)) = v89 else { return Ok(None); }
;
let v92 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v93 != v95 { return Ok(None); }
let v96 = match s.unapply(v94) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v97, v98)) = v96 else { return Ok(None); }
;
let v99 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v97 != v99 { return Ok(None); }
let v100 = match s.unapply(v98) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v101, v102)) = v100 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v101, a3, v102, a2, a4, v91, v84, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s: &mut Store, v69: Term, v70: Term, a2: Term, v67: Term, a4: Term, v49: Term, a10: Term, a7: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v71 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a2 { return Ok(None); }
if v67 != a4 { return Ok(None); }
let v72 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v72 { return Ok(None); }
let v73 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v73 else { return Ok(None); }
;
let v74 = fields[0];
let v75 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v76, v77)) = v75 else { return Ok(None); }
;
let v78 = match s.unapply(v76) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v79 != v81 { return Ok(None); }
if v80 != a7 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup2(s, v77, a3, a2, a4, a1, a0, a5, a6, a7)
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
pub(super) fn case_346_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v229: Term, v242: Term, v220: Term, v219: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v243 = match s.apply(v229, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v220, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v244, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v219, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v196, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v173, v248) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v249))
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v230: Term, a4: Term, a9: Term, a0: Term, a1: Term, v229: Term, v220: Term, v219: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v231 = match s.apply(v230, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_extract, &[a9, v233]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.builtin_list(EvalOp::ListConcat, &[v236, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.builtin_list(EvalOp::ListSingletonElim, &[v235, v237]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v234, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match eo__24eo_5ftypeof(s, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match eo__24eo_5fnil(s, v232, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v231, v241) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v229, v242, v220, v219, v196, v173)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v197: Term, v218: Term, a9: Term, a0: Term, a1: Term, a4: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v219 = match s.apply(v197, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_extract, &[a9, v222]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_list(EvalOp::ListConcat, &[v225, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_list(EvalOp::ListSingletonElim, &[v224, v226]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v223, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v221, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v230, a4, a9, a0, a1, v229, v220, v219, v196, v173)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v206: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v205: Term, v197: Term, a9: Term, a4: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v207 = match s.apply(v206, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_list(EvalOp::ListConcat, &[v211, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_list(EvalOp::ListSingletonElim, &[v210, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v209, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match eo__24eo_5ftypeof(s, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match eo__24eo_5fnil(s, v208, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v207, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v205, v217) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v197, v218, a9, a0, a1, a4, v196, v173)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v182: Term, v194: Term, v174: Term, a7: Term, a8: Term, a0: Term, a1: Term, a2: Term, a9: Term, a4: Term, v173: Term) -> CheckResult<Option<Term>> {
let v195 = match s.apply(v182, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v174, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.builtin_list(EvalOp::ListConcat, &[v201, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.builtin_list(EvalOp::ListSingletonElim, &[v200, v202]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v199, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v198, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v206, a2, a7, a8, a0, a1, v205, v197, a9, a4, v196, v173)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v182: Term, v174: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v173: Term) -> CheckResult<Option<Term>> {
let v183 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_list(EvalOp::ListConcat, &[v188, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.builtin_list(EvalOp::ListSingletonElim, &[v187, v189]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v186, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match eo__24eo_5ftypeof(s, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24eo_5fnil(s, v185, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v184, v193) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v182, v194, v174, a7, a8, a0, a1, a2, a9, a4, v173)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v170: Term, a1: Term, v158: Term, a0: Term, v157: Term, a5: Term, a6: Term, a3: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term) -> CheckResult<Option<Term>> {
let v171 = match s.apply(v170, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.builtin_list(EvalOp::ListConcat, &[v158, a0, v171]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v157, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_list(EvalOp::ListConcat, &[v178, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.builtin_list(EvalOp::ListSingletonElim, &[v177, v179]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v176, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v175, v181) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v182, v174, a7, a8, a2, a9, a4, v173)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v158: Term, a0: Term, v157: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v159 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v162, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v164, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v165, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v163, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v161, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v159, v169) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v170, a1, v158, a0, v157, a5, a6, a3, a7, a8, a2, a9, a4)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v140: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v145 = match s.unapply(v140) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v146, v147)) = v145 else { return Ok(None); }
;
let v148 = match s.unapply(v146) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v149, v150)) = v148 else { return Ok(None); }
;
let v151 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v149 != v151 { return Ok(None); }
let v152 = match s.unapply(v150) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v153, v154)) = v152 else { return Ok(None); }
;
let v155 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v153 != v155 { return Ok(None); }
if v154 != a4 { return Ok(None); }
let v156 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v147 != v156 { return Ok(None); }
let v157 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, a3, a2, a4, a1, v158, a0, v157, a5, a6, a7, a8, a9)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v129: Term, v131: Term, v130: Term, a8: Term, v127: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v129 != v131 { return Ok(None); }
if v130 != a8 { return Ok(None); }
let v132 = match s.unapply(v127) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v133, v134)) = v132 else { return Ok(None); }
;
let v135 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v133 != v135 { return Ok(None); }
if v134 != a4 { return Ok(None); }
let v136 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v136 else { return Ok(None); }
;
let v137 = fields[0];
let v138 = match s.unapply(v137) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v139, v140)) = v138 else { return Ok(None); }
;
let v141 = match s.unapply(v139) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v142, v143)) = v141 else { return Ok(None); }
;
let v144 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v142 != v144 { return Ok(None); }
if v143 != a9 { return Ok(None); }
more_8_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v140, a4, a3, a2, a1, a0, a5, a6, a7, a8, a9)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v115: Term, a4: Term, v112: Term, v94: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v117 = match s.unapply(v115) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v118, v119)) = v117 else { return Ok(None); }
;
let v120 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v118 != v120 { return Ok(None); }
if v119 != a4 { return Ok(None); }
let v121 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v112 != v121 { return Ok(None); }
let v122 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v122 { return Ok(None); }
let v123 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v123 else { return Ok(None); }
;
let v124 = fields[0];
let v125 = match s.unapply(v124) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v126, v127)) = v125 else { return Ok(None); }
;
let v128 = match s.unapply(v126) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v129, v130)) = v128 else { return Ok(None); }
;
let v131 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v129, v131, v130, a8, v127, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v97: Term, a2: Term, a4: Term, v94: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v99 = match s.unapply(v97) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v100, v101)) = v99 else { return Ok(None); }
;
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v103 != v105 { return Ok(None); }
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v107 != v109 { return Ok(None); }
if v108 != a2 { return Ok(None); }
let v110 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.unapply(v111) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v114 != v116 { return Ok(None); }
more_6_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v115, a4, v112, v94, a13, a8, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v73: Term, a12: Term, a7: Term, a2: Term, a4: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v82 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v82 { return Ok(None); }
let v83 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v83 else { return Ok(None); }
;
let v84 = fields[0];
let v85 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v89 != v91 { return Ok(None); }
if v90 != a7 { return Ok(None); }
let v92 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.unapply(v93) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v96 != v98 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v97, a2, a4, v94, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v65: Term, a2: Term, v62: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v67 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
let v70 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v68 != v70 { return Ok(None); }
if v69 != a2 { return Ok(None); }
let v71 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v72, v73)) = v71 else { return Ok(None); }
;
let v74 = match s.unapply(v72) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v75, v76)) = v74 else { return Ok(None); }
;
let v77 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v77 { return Ok(None); }
let v78 = match s.unapply(v76) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v79 != v81 { return Ok(None); }
if v80 != a4 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v73, a12, a7, a2, a4, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s: &mut Store, v11: Term, a11: Term, a6: Term, a2: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v50 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v50 { return Ok(None); }
let v51 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v51 else { return Ok(None); }
;
let v52 = fields[0];
let v53 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.unapply(v54) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v57, v58)) = v56 else { return Ok(None); }
;
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v59 { return Ok(None); }
if v58 != a6 { return Ok(None); }
let v60 = match s.unapply(v55) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.unapply(v61) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v64, v65)) = v63 else { return Ok(None); }
;
let v66 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v64 != v66 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dand_2dconcat_2dpullup3(s, v65, a2, v62, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
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
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v49 { return Ok(None); }
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
pub(super) fn case_347_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_86_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_344_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_345_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_346_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_347_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v229: Term, v242: Term, v220: Term, v219: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v243 = match s.apply(v229, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v220, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v244, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v219, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v196, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v173, v248) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v249))
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v230: Term, a4: Term, a9: Term, a0: Term, a1: Term, v229: Term, v220: Term, v219: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v231 = match s.apply(v230, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_extract, &[a9, v233]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.builtin_list(EvalOp::ListConcat, &[v236, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.builtin_list(EvalOp::ListSingletonElim, &[v235, v237]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v234, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match eo__24eo_5ftypeof(s, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match eo__24eo_5fnil(s, v232, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v231, v241) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v229, v242, v220, v219, v196, v173)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v197: Term, v218: Term, a9: Term, a0: Term, a1: Term, a4: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v219 = match s.apply(v197, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_extract, &[a9, v222]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_list(EvalOp::ListConcat, &[v225, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_list(EvalOp::ListSingletonElim, &[v224, v226]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v223, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v221, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v230, a4, a9, a0, a1, v229, v220, v219, v196, v173)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v206: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v205: Term, v197: Term, a9: Term, a4: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v207 = match s.apply(v206, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_list(EvalOp::ListConcat, &[v211, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_list(EvalOp::ListSingletonElim, &[v210, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v209, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match eo__24eo_5ftypeof(s, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match eo__24eo_5fnil(s, v208, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v207, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v205, v217) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v197, v218, a9, a0, a1, a4, v196, v173)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v182: Term, v194: Term, v174: Term, a7: Term, a8: Term, a0: Term, a1: Term, a2: Term, a9: Term, a4: Term, v173: Term) -> CheckResult<Option<Term>> {
let v195 = match s.apply(v182, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v174, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.builtin_list(EvalOp::ListConcat, &[v201, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.builtin_list(EvalOp::ListSingletonElim, &[v200, v202]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v199, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v198, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v206, a2, a7, a8, a0, a1, v205, v197, a9, a4, v196, v173)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v182: Term, v174: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v173: Term) -> CheckResult<Option<Term>> {
let v183 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_list(EvalOp::ListConcat, &[v188, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.builtin_list(EvalOp::ListSingletonElim, &[v187, v189]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v186, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match eo__24eo_5ftypeof(s, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24eo_5fnil(s, v185, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v184, v193) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v182, v194, v174, a7, a8, a0, a1, a2, a9, a4, v173)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v170: Term, a1: Term, v158: Term, a0: Term, v157: Term, a5: Term, a6: Term, a3: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term) -> CheckResult<Option<Term>> {
let v171 = match s.apply(v170, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.builtin_list(EvalOp::ListConcat, &[v158, a0, v171]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v157, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_list(EvalOp::ListConcat, &[v178, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.builtin_list(EvalOp::ListSingletonElim, &[v177, v179]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v176, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v175, v181) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v182, v174, a7, a8, a2, a9, a4, v173)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v158: Term, a0: Term, v157: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v159 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v162, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v164, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v165, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v163, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v161, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v159, v169) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v170, a1, v158, a0, v157, a5, a6, a3, a7, a8, a2, a9, a4)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v140: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v145 = match s.unapply(v140) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v146, v147)) = v145 else { return Ok(None); }
;
let v148 = match s.unapply(v146) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v149, v150)) = v148 else { return Ok(None); }
;
let v151 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v149 != v151 { return Ok(None); }
let v152 = match s.unapply(v150) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v153, v154)) = v152 else { return Ok(None); }
;
let v155 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v153 != v155 { return Ok(None); }
if v154 != a4 { return Ok(None); }
let v156 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v147 != v156 { return Ok(None); }
let v157 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, a3, a2, a4, a1, v158, a0, v157, a5, a6, a7, a8, a9)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v129: Term, v131: Term, v130: Term, a8: Term, v127: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v129 != v131 { return Ok(None); }
if v130 != a8 { return Ok(None); }
let v132 = match s.unapply(v127) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v133, v134)) = v132 else { return Ok(None); }
;
let v135 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v133 != v135 { return Ok(None); }
if v134 != a4 { return Ok(None); }
let v136 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v136 else { return Ok(None); }
;
let v137 = fields[0];
let v138 = match s.unapply(v137) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v139, v140)) = v138 else { return Ok(None); }
;
let v141 = match s.unapply(v139) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v142, v143)) = v141 else { return Ok(None); }
;
let v144 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v142 != v144 { return Ok(None); }
if v143 != a9 { return Ok(None); }
more_8_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v140, a4, a3, a2, a1, a0, a5, a6, a7, a8, a9)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v115: Term, a4: Term, v112: Term, v94: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v117 = match s.unapply(v115) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v118, v119)) = v117 else { return Ok(None); }
;
let v120 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v118 != v120 { return Ok(None); }
if v119 != a4 { return Ok(None); }
let v121 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v112 != v121 { return Ok(None); }
let v122 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v122 { return Ok(None); }
let v123 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v123 else { return Ok(None); }
;
let v124 = fields[0];
let v125 = match s.unapply(v124) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v126, v127)) = v125 else { return Ok(None); }
;
let v128 = match s.unapply(v126) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v129, v130)) = v128 else { return Ok(None); }
;
let v131 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v129, v131, v130, a8, v127, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v97: Term, a2: Term, a4: Term, v94: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v99 = match s.unapply(v97) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v100, v101)) = v99 else { return Ok(None); }
;
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v103 != v105 { return Ok(None); }
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v107 != v109 { return Ok(None); }
if v108 != a2 { return Ok(None); }
let v110 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.unapply(v111) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v114 != v116 { return Ok(None); }
more_6_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v115, a4, v112, v94, a13, a8, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v73: Term, a12: Term, a7: Term, a2: Term, a4: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v82 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v82 { return Ok(None); }
let v83 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v83 else { return Ok(None); }
;
let v84 = fields[0];
let v85 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v89 != v91 { return Ok(None); }
if v90 != a7 { return Ok(None); }
let v92 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.unapply(v93) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v96 != v98 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v97, a2, a4, v94, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v65: Term, a2: Term, v62: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v67 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
let v70 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v68 != v70 { return Ok(None); }
if v69 != a2 { return Ok(None); }
let v71 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v72, v73)) = v71 else { return Ok(None); }
;
let v74 = match s.unapply(v72) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v75, v76)) = v74 else { return Ok(None); }
;
let v77 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v77 { return Ok(None); }
let v78 = match s.unapply(v76) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v79 != v81 { return Ok(None); }
if v80 != a4 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v73, a12, a7, a2, a4, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s: &mut Store, v11: Term, a11: Term, a6: Term, a2: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v50 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v50 { return Ok(None); }
let v51 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v51 else { return Ok(None); }
;
let v52 = fields[0];
let v53 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.unapply(v54) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v57, v58)) = v56 else { return Ok(None); }
;
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v59 { return Ok(None); }
if v58 != a6 { return Ok(None); }
let v60 = match s.unapply(v55) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.unapply(v61) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v64, v65)) = v63 else { return Ok(None); }
;
let v66 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v64 != v66 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dor_2dconcat_2dpullup3(s, v65, a2, v62, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
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
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v49 { return Ok(None); }
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
pub(super) fn case_348_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v229: Term, v242: Term, v220: Term, v219: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v243 = match s.apply(v229, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v220, v243) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v244, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.apply(v219, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v196, v247) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.apply(v173, v248) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v249))
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v230: Term, a4: Term, a9: Term, a0: Term, a1: Term, v229: Term, v220: Term, v219: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v231 = match s.apply(v230, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_extract, &[a9, v233]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.builtin_list(EvalOp::ListConcat, &[v236, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.builtin_list(EvalOp::ListSingletonElim, &[v235, v237]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v234, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match eo__24eo_5ftypeof(s, v239) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match eo__24eo_5fnil(s, v232, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v231, v241) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v229, v242, v220, v219, v196, v173)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v197: Term, v218: Term, a9: Term, a0: Term, a1: Term, a4: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v219 = match s.apply(v197, v218) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_extract, &[a9, v222]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.builtin_list(EvalOp::ListConcat, &[v225, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.builtin_list(EvalOp::ListSingletonElim, &[v224, v226]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v223, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v221, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v230, a4, a9, a0, a1, v229, v220, v219, v196, v173)
}
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v206: Term, a2: Term, a7: Term, a8: Term, a0: Term, a1: Term, v205: Term, v197: Term, a9: Term, a4: Term, v196: Term, v173: Term) -> CheckResult<Option<Term>> {
let v207 = match s.apply(v206, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_list(EvalOp::ListConcat, &[v211, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_list(EvalOp::ListSingletonElim, &[v210, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.apply(v209, v213) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match eo__24eo_5ftypeof(s, v214) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match eo__24eo_5fnil(s, v208, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v207, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v205, v217) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v197, v218, a9, a0, a1, a4, v196, v173)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v182: Term, v194: Term, v174: Term, a7: Term, a8: Term, a0: Term, a1: Term, a2: Term, a9: Term, a4: Term, v173: Term) -> CheckResult<Option<Term>> {
let v195 = match s.apply(v182, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.apply(v174, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.construct(Constructor::eo_extract, &[a7, a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.builtin_list(EvalOp::ListConcat, &[v201, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.builtin_list(EvalOp::ListSingletonElim, &[v200, v202]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v199, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v198, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v206, a2, a7, a8, a0, a1, v205, v197, a9, a4, v196, v173)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a5: Term, a6: Term, a0: Term, a1: Term, v182: Term, v174: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term, v173: Term) -> CheckResult<Option<Term>> {
let v183 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.apply(v183, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.builtin_list(EvalOp::ListConcat, &[v188, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.builtin_list(EvalOp::ListSingletonElim, &[v187, v189]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v186, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match eo__24eo_5ftypeof(s, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24eo_5fnil(s, v185, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v184, v193) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v182, v194, v174, a7, a8, a0, a1, a2, a9, a4, v173)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v170: Term, a1: Term, v158: Term, a0: Term, v157: Term, a5: Term, a6: Term, a3: Term, a7: Term, a8: Term, a2: Term, a9: Term, a4: Term) -> CheckResult<Option<Term>> {
let v171 = match s.apply(v170, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.builtin_list(EvalOp::ListConcat, &[v158, a0, v171]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v157, v172) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.builtin_list(EvalOp::ListConcat, &[v178, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.builtin_list(EvalOp::ListSingletonElim, &[v177, v179]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v176, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v175, v181) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a3, a5, a6, a0, a1, v182, v174, a7, a8, a2, a9, a4, v173)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, a3: Term, a2: Term, a4: Term, a1: Term, v158: Term, a0: Term, v157: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v159 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v162, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v164, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v165, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v163, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v161, v168) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v159, v169) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v170, a1, v158, a0, v157, a5, a6, a3, a7, a8, a2, a9, a4)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v140: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
let v145 = match s.unapply(v140) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v146, v147)) = v145 else { return Ok(None); }
;
let v148 = match s.unapply(v146) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v149, v150)) = v148 else { return Ok(None); }
;
let v151 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v149 != v151 { return Ok(None); }
let v152 = match s.unapply(v150) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v153, v154)) = v152 else { return Ok(None); }
;
let v155 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v153 != v155 { return Ok(None); }
if v154 != a4 { return Ok(None); }
let v156 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v147 != v156 { return Ok(None); }
let v157 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, a3, a2, a4, a1, v158, a0, v157, a5, a6, a7, a8, a9)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v129: Term, v131: Term, v130: Term, a8: Term, v127: Term, a4: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
if v129 != v131 { return Ok(None); }
if v130 != a8 { return Ok(None); }
let v132 = match s.unapply(v127) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v133, v134)) = v132 else { return Ok(None); }
;
let v135 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v133 != v135 { return Ok(None); }
if v134 != a4 { return Ok(None); }
let v136 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v136 else { return Ok(None); }
;
let v137 = fields[0];
let v138 = match s.unapply(v137) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v139, v140)) = v138 else { return Ok(None); }
;
let v141 = match s.unapply(v139) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v142, v143)) = v141 else { return Ok(None); }
;
let v144 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v142 != v144 { return Ok(None); }
if v143 != a9 { return Ok(None); }
more_8_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v140, a4, a3, a2, a1, a0, a5, a6, a7, a8, a9)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v115: Term, a4: Term, v112: Term, v94: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v117 = match s.unapply(v115) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v118, v119)) = v117 else { return Ok(None); }
;
let v120 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v118 != v120 { return Ok(None); }
if v119 != a4 { return Ok(None); }
let v121 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v112 != v121 { return Ok(None); }
let v122 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v122 { return Ok(None); }
let v123 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v123 else { return Ok(None); }
;
let v124 = fields[0];
let v125 = match s.unapply(v124) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v126, v127)) = v125 else { return Ok(None); }
;
let v128 = match s.unapply(v126) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v129, v130)) = v128 else { return Ok(None); }
;
let v131 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v129, v131, v130, a8, v127, a4, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v97: Term, a2: Term, a4: Term, v94: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v99 = match s.unapply(v97) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v100, v101)) = v99 else { return Ok(None); }
;
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v103 != v105 { return Ok(None); }
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v107 != v109 { return Ok(None); }
if v108 != a2 { return Ok(None); }
let v110 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.unapply(v111) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v114 != v116 { return Ok(None); }
more_6_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v115, a4, v112, v94, a13, a8, a14, a9, a3, a2, a1, a0, a5, a6, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v73: Term, a12: Term, a7: Term, a2: Term, a4: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v82 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v82 { return Ok(None); }
let v83 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v83 else { return Ok(None); }
;
let v84 = fields[0];
let v85 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v89 != v91 { return Ok(None); }
if v90 != a7 { return Ok(None); }
let v92 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.unapply(v93) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v96 != v98 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v97, a2, a4, v94, a13, a8, a14, a9, a3, a1, a0, a5, a6, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v65: Term, a2: Term, v62: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v67 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
let v70 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v68 != v70 { return Ok(None); }
if v69 != a2 { return Ok(None); }
let v71 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v72, v73)) = v71 else { return Ok(None); }
;
let v74 = match s.unapply(v72) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v75, v76)) = v74 else { return Ok(None); }
;
let v77 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v77 { return Ok(None); }
let v78 = match s.unapply(v76) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v79 != v81 { return Ok(None); }
if v80 != a4 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v73, a12, a7, a2, a4, a13, a8, a14, a9, a3, a1, a0, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s: &mut Store, v11: Term, a11: Term, a6: Term, a2: Term, a4: Term, a12: Term, a7: Term, a13: Term, a8: Term, a14: Term, a9: Term, a3: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v50 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v50 { return Ok(None); }
let v51 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v51 else { return Ok(None); }
;
let v52 = fields[0];
let v53 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.unapply(v54) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v57, v58)) = v56 else { return Ok(None); }
;
let v59 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v59 { return Ok(None); }
if v58 != a6 { return Ok(None); }
let v60 = match s.unapply(v55) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.unapply(v61) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v64, v65)) = v63 else { return Ok(None); }
;
let v66 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v64 != v66 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dxor_2dconcat_2dpullup3(s, v65, a2, v62, a4, a12, a7, a13, a8, a14, a9, a3, a1, a0, a5, a6)
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
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v49 { return Ok(None); }
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
pub(super) fn case_349_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s: &mut Store, v23: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
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
let v25 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dxor_2dduplicate(s, v23, v26)
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
pub(super) fn case_350_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, v21: Term, v28: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v21, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_list(EvalOp::ListConcat, &[v32, a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_list(EvalOp::ListSingletonElim, &[v31, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v30, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v36))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dones(s: &mut Store, v17: Term, v19: Term, v18: Term, a3: Term, v11: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a3 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_list(EvalOp::ListConcat, &[v22, a0, v27]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dxor_2dones(s, v21, v28, a0, a1)
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
pub(super) fn case_351_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_352_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_353_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s: &mut Store, v11: Term, v10: Term, v8: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v7, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dult_2dzero_2d1(s, v11, v10, v8, v7)
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
pub(super) fn case_354_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
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
pub(super) fn case_355_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_88_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_352_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_353_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_354_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_355_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
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
pub(super) fn case_356_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_357_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_358_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dule_2dzero(s: &mut Store, v10: Term, v11: Term, v9: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v7, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dule_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dule_2dzero(s, v10, v11, v9, v7)
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
pub(super) fn case_359_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_89_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_356_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_357_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_358_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_359_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dule(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
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
pub(super) fn case_360_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_361_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, v44: Term) -> CheckResult<Option<Term>> {
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v46))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dule_2dmax(s: &mut Store, v34: Term, v35: Term, a0: Term, v24: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a0 { return Ok(None); }
let v37 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v37 { return Ok(None); }
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v38, v43) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dule_2dmax(s, v44)
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
pub(super) fn case_362_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_363_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_90_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_360_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_361_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_362_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_363_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v83: Term, v84: Term, v78: Term, v66: Term) -> CheckResult<Option<Term>> {
let v85 = match s.apply(v83, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v78, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v66, v86) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v87))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v72: Term, a2: Term, a1: Term, v71: Term, a0: Term, v70: Term, v69: Term, v67: Term, a5: Term, v66: Term) -> CheckResult<Option<Term>> {
let v73 = match s.apply(v72, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_list(EvalOp::ListConcat, &[v71, a0, v74]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.builtin_list(EvalOp::ListSingletonElim, &[v70, v75]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v69, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v67, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v79, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v83, v84, v78, v66)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v60: Term, a4: Term, v59: Term, a1: Term, v58: Term, v56: Term, a0: Term, v55: Term, a6: Term, a2: Term, a5: Term) -> CheckResult<Option<Term>> {
let v61 = match s.apply(v60, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v58, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.builtin_list(EvalOp::ListConcat, &[v56, a0, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v55, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_extract, &[a6, v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v72, a2, a1, v71, a0, v70, v69, v67, a5, v66)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s: &mut Store, v45: Term, a4: Term, v38: Term, a2: Term, a3: Term, a1: Term, a0: Term, a6: Term, a5: Term) -> CheckResult<Option<Term>> {
let v50 = match s.unapply(v45) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v53 { return Ok(None); }
if v52 != a4 { return Ok(None); }
let v54 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v54 { return Ok(None); }
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d1(s, v60, a4, v59, a1, v58, v56, a0, v55, a6, a2, a5)
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
pub(super) fn more_74_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_364_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_74_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v114: Term, v117: Term, v113: Term, v99: Term) -> CheckResult<Option<Term>> {
let v118 = match s.apply(v114, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v118, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v113, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v99, v121) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v122))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, a2: Term, a1: Term, v105: Term, a0: Term, v104: Term, v103: Term, v102: Term, v100: Term, a5: Term, v99: Term) -> CheckResult<Option<Term>> {
let v106 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.builtin_list(EvalOp::ListConcat, &[v105, a0, v108]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.builtin_list(EvalOp::ListSingletonElim, &[v104, v109]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v103, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v102, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v100, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v115, v116) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v114, v117, v113, v99)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v93: Term, a4: Term, v92: Term, a1: Term, v91: Term, v89: Term, a0: Term, v88: Term, a6: Term, a2: Term, a5: Term) -> CheckResult<Option<Term>> {
let v94 = match s.apply(v93, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v92, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v91, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.builtin_list(EvalOp::ListConcat, &[v89, a0, v97]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v88, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_extract, &[a6, v101]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, a2, a1, v105, a0, v104, v103, v102, v100, a5, v99)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v84: Term, v85: Term, a3: Term, v78: Term, a4: Term, v60: Term, a2: Term, a1: Term, a0: Term, a6: Term, a5: Term) -> CheckResult<Option<Term>> {
let v86 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v86 { return Ok(None); }
if v85 != a3 { return Ok(None); }
if v78 != a4 { return Ok(None); }
let v87 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v87 { return Ok(None); }
let v88 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v93, a4, v92, a1, v91, v89, a0, v88, a6, a2, a5)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v66: Term, a3: Term, v67: Term, a4: Term, v60: Term, a2: Term, a1: Term, a0: Term, a6: Term, a5: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v84, v85, a3, v78, a4, v60, a2, a1, a0, a6, a5)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v40: Term, a4: Term, a9: Term, a6: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v66, a3, v67, a4, v60, a2, a1, a0, a6, a5)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v32: Term, a5: Term, v29: Term, a3: Term, a4: Term, a9: Term, a6: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v40, a4, a9, a6, a3, a2, a1, a0, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s: &mut Store, v18: Term, a3: Term, v15: Term, a4: Term, v4: Term, a8: Term, a5: Term, a9: Term, a6: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a3 { return Ok(None); }
if v15 != a4 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v32, a5, v29, a3, a4, a9, a6, a2, a1, a0)
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
more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2(s, v18, a3, v15, a4, v4, a8, a5, a9, a6, a2, a1, a0)
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
pub(super) fn more_75_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_365_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_75_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v103: Term, v105: Term, v101: Term, a3: Term, v100: Term) -> CheckResult<Option<Term>> {
let v106 = match s.apply(v103, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v101, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v109, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v108, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v107, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v100, v115) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v116))
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v91: Term, v93: Term, a0: Term, v90: Term, v88: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
let v94 = match s.apply(v91, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match eo__24eo_5fnil(s, v95, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v94, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v90, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v88, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_extract, &[a4, v102]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v103, v105, v101, a3, v100)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v84: Term, v85: Term, a1: Term, v78: Term, a2: Term, v60: Term, a0: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
let v86 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v86 { return Ok(None); }
if v85 != a1 { return Ok(None); }
if v78 != a2 { return Ok(None); }
let v87 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v87 { return Ok(None); }
let v88 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v91, v93, a0, v90, v88, a4, a3)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v66: Term, a1: Term, v67: Term, a2: Term, v60: Term, a0: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_4_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v84, v85, a1, v78, a2, v60, a0, a4, a3)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v40: Term, a2: Term, a7: Term, a4: Term, a1: Term, a0: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_3_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v66, a1, v67, a2, v60, a0, a4, a3)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v32: Term, a3: Term, v29: Term, a1: Term, a2: Term, a7: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
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
more_2_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v40, a2, a7, a4, a1, a0, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s: &mut Store, v18: Term, a1: Term, v15: Term, a2: Term, v4: Term, a6: Term, a3: Term, a7: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a1 { return Ok(None); }
if v15 != a2 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
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
more_1_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v32, a3, v29, a1, a2, a7, a4, a0)
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
more_0_eo__24eo_5fprog_5fbv_2dmult_2dpow2_2d2b(s, v18, a1, v15, a2, v4, a6, a3, a7, a4, a0)
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
pub(super) fn more_76_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_366_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_76_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn more_22_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v350: Term, v353: Term) -> CheckResult<Option<Term>> {
let v354 = match s.apply(v350, v353) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v354))
}
pub(super) fn more_21_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v341: Term, v339: Term, v335: Term, v334: Term, v323: Term, v312: Term, v311: Term, a8: Term) -> CheckResult<Option<Term>> {
let v342 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match s.apply(v341, v342) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match s.apply(v339, v343) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match eo__24eo_5ftypeof(s, v344) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match eo__24eo_5fnil(s, v335, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.apply(v334, v346) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match s.apply(v323, v347) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.apply(v312, v348) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.apply(v311, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a8]) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.apply(v351, v352) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v350, v353)
}
pub(super) fn more_20_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v329: Term, a7: Term, v328: Term, v324: Term, a3: Term, a2: Term, a4: Term, v323: Term, v312: Term, v311: Term, a8: Term) -> CheckResult<Option<Term>> {
let v330 = match s.apply(v329, a7) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match s.apply(v330, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.apply(v328, v332) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.apply(v324, v333) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match s.apply(v337, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.apply(v336, v338) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.apply(v340, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v341, v339, v335, v334, v323, v312, v311, a8)
}
pub(super) fn more_19_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, a4: Term, v317: Term, v313: Term, a6: Term, a5: Term, a7: Term, a3: Term, a2: Term, v312: Term, v311: Term, a8: Term) -> CheckResult<Option<Term>> {
let v318 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.apply(v318, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.apply(v319, v320) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.apply(v317, v321) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.apply(v313, v322) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.apply(v326, a5) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.apply(v325, v327) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v329, a7, v328, v324, a3, a2, a4, v323, v312, v311, a8)
}
pub(super) fn more_18_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v307: Term, v309: Term, v308: Term, a0: Term, v305: Term, a1: Term, v298: Term, a3: Term, a2: Term, a4: Term, a6: Term, a5: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
if v307 != v309 { return Ok(None); }
if v308 != a0 { return Ok(None); }
if v305 != a1 { return Ok(None); }
let v310 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v298 != v310 { return Ok(None); }
let v311 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.construct(Constructor::eo_extract, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.apply(v315, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v317 = match s.apply(v314, v316) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, a4, v317, v313, a6, a5, a7, a3, a2, v312, v311, a8)
}
pub(super) fn more_17_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v289: Term, v290: Term, a0: Term, a1: Term, a3: Term, a2: Term, a4: Term, a6: Term, a5: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
let v291 = match s.unapply(v289) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v292, v293)) = v291 else { return Ok(None); }
;
let v294 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v292 != v294 { return Ok(None); }
let v295 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v293 != v295 { return Ok(None); }
let v296 = match s.unapply(v290) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v297, v298)) = v296 else { return Ok(None); }
;
let v299 = match s.unapply(v297) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v300, v301)) = v299 else { return Ok(None); }
;
let v302 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v300 != v302 { return Ok(None); }
let v303 = match s.unapply(v301) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v304, v305)) = v303 else { return Ok(None); }
;
let v306 = match s.unapply(v304) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v307, v308)) = v306 else { return Ok(None); }
;
let v309 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v307, v309, v308, a0, v305, a1, v298, a3, a2, a4, a6, a5, a7, a8)
}
pub(super) fn more_16_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v227: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a3: Term, a2: Term, a4: Term, a6: Term, a5: Term, a7: Term) -> CheckResult<Option<Term>> {
let v277 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v227 != v277 { return Ok(None); }
if v126 != a1 { return Ok(None); }
let v278 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v119 != v278 { return Ok(None); }
let v279 = match s.destruct(Constructor::eo__24eo_5fpf, a15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v279 else { return Ok(None); }
;
let v280 = fields[0];
let v281 = match s.unapply(v280) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v282, v283)) = v281 else { return Ok(None); }
;
let v284 = match s.unapply(v282) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v285, v286)) = v284 else { return Ok(None); }
;
let v287 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v285 != v287 { return Ok(None); }
if v286 != a8 { return Ok(None); }
let v288 = match s.unapply(v283) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v289, v290)) = v288 else { return Ok(None); }
;
more_17_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v289, v290, a0, a1, a3, a2, a4, a6, a5, a7, a8)
}
pub(super) fn more_15_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v262: Term, v259: Term, a5: Term, v227: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a3: Term, a2: Term, a4: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
let v264 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v262 != v264 { return Ok(None); }
let v265 = match s.unapply(v259) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v266, v267)) = v265 else { return Ok(None); }
;
let v268 = match s.unapply(v266) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v269, v270)) = v268 else { return Ok(None); }
;
let v271 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v269 != v271 { return Ok(None); }
let v272 = match s.unapply(v270) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v273, v274)) = v272 else { return Ok(None); }
;
let v275 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v273 != v275 { return Ok(None); }
if v274 != a5 { return Ok(None); }
let v276 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v267 != v276 { return Ok(None); }
more_16_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v227, v126, a1, v119, a15, a8, a0, a3, a2, a4, a6, a5, a7)
}
pub(super) fn more_14_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v244: Term, v237: Term, a6: Term, v234: Term, a5: Term, v227: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a3: Term, a2: Term, a4: Term, a7: Term) -> CheckResult<Option<Term>> {
let v249 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v244 != v249 { return Ok(None); }
if v237 != a6 { return Ok(None); }
let v250 = match s.unapply(v234) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v251, v252)) = v250 else { return Ok(None); }
;
let v253 = match s.unapply(v251) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v254, v255)) = v253 else { return Ok(None); }
;
let v256 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v254 != v256 { return Ok(None); }
if v255 != a6 { return Ok(None); }
let v257 = match s.unapply(v252) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v258, v259)) = v257 else { return Ok(None); }
;
let v260 = match s.unapply(v258) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v261, v262)) = v260 else { return Ok(None); }
;
let v263 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v261 != v263 { return Ok(None); }
more_15_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v262, v259, a5, v227, v126, a1, v119, a15, a8, a0, a3, a2, a4, a6, a7)
}
