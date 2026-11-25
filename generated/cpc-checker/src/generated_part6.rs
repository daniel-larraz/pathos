//! Generated functions, module 6 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn case_192_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fabs_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dabs_2deq(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_3_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s: &mut Store, a1: Term, v47: Term, v43: Term, v31: Term, v8: Term) -> CheckResult<Option<Term>> {
let v48 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v43, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v31, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v8, v52) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v53))
}
pub(super) fn more_2_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s: &mut Store, v34: Term, v35: Term, v32: Term, a0: Term, a1: Term, v31: Term, v8: Term) -> CheckResult<Option<Term>> {
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v32, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v37, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v44, v46) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s, a1, v47, v43, v31, v8)
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s: &mut Store, v20: Term, v23: Term, a0: Term, a1: Term, v14: Term, v8: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v24, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v14, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s, v34, v35, v32, a0, a1, v31, v8)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s: &mut Store, v11: Term, v9: Term, a1: Term, a0: Term, v8: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s, v20, v23, a0, a1, v14, v8)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s, v11, v9, a1, a0, v8)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-abs-int-gt"
pub fn eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s, a0, a1);
s.leave();
result
}
pub(super) fn case_193_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fabs_5fint_5fgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dabs_2dint_2dgt(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_3_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s: &mut Store, a1: Term, v50: Term, v46: Term, v33: Term, v8: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v50, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v46, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v33, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v8, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v56))
}
pub(super) fn more_2_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s: &mut Store, v36: Term, v38: Term, v34: Term, a0: Term, a1: Term, v33: Term, v8: Term) -> CheckResult<Option<Term>> {
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v34, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v40, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s, a1, v50, v46, v33, v8)
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s: &mut Store, v22: Term, v25: Term, a0: Term, a1: Term, v15: Term, v8: Term) -> CheckResult<Option<Term>> {
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v26, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v15, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v38 = match s.literal(Lit::Rational(v37)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s, v36, v38, v34, a0, a1, v33, v8)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s: &mut Store, v11: Term, v9: Term, a1: Term, a0: Term, v8: Term) -> CheckResult<Option<Term>> {
let v12 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v13 = match s.literal(Lit::Rational(v12)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v9, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v20 = match s.literal(Lit::Rational(v19)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v16, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s, v22, v25, a0, a1, v15, v8)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s, v11, v9, a1, a0, v8)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-abs-real-gt"
pub fn eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s, a0, a1);
s.leave();
result
}
pub(super) fn case_194_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fabs_5freal_5fgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dabs_2dreal_2dgt(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s: &mut Store, v11: Term, a1: Term, a3: Term, v10: Term, a2: Term, v8: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v8, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s, v11, a1, a3, v10, a2, v8)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-geq-ite-lift"
pub fn eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_195_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fgeq_5fite_5flift, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5farith_2dgeq_2dite_2dlift(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_48_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_192_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_193_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_194_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_195_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s: &mut Store, v11: Term, a1: Term, a3: Term, v10: Term, a2: Term, v8: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v8, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s, v11, a1, a3, v10, a2, v8)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-leq-ite-lift"
pub fn eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_196_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fleq_5fite_5flift, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5farith_2dleq_2dite_2dlift(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dmin_2dlt1(s: &mut Store, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dmin_2dlt1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dmin_2dlt1(s, v11)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dmin_2dlt1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dmin_2dlt1(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-min-lt1"
pub fn eo__24eo_5fprog_5farith_2dmin_2dlt1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dmin_2dlt1(s, a0, a1);
s.leave();
result
}
pub(super) fn case_197_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmin_5flt1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dmin_2dlt1(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dmin_2dlt2(s: &mut Store, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dmin_2dlt2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dmin_2dlt2(s, v11)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dmin_2dlt2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dmin_2dlt2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-min-lt2"
pub fn eo__24eo_5fprog_5farith_2dmin_2dlt2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dmin_2dlt2(s, a0, a1);
s.leave();
result
}
pub(super) fn case_198_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmin_5flt2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dmin_2dlt2(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dmax_2dgeq1(s: &mut Store, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dmax_2dgeq1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dmax_2dgeq1(s, v11)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dmax_2dgeq1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dmax_2dgeq1(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-max-geq1"
pub fn eo__24eo_5fprog_5farith_2dmax_2dgeq1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dmax_2dgeq1(s, a0, a1);
s.leave();
result
}
pub(super) fn case_199_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmax_5fgeq1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dmax_2dgeq1(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_49_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_196_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_197_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_198_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_199_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dmax_2dgeq2(s: &mut Store, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dmax_2dgeq2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dmax_2dgeq2(s, v11)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dmax_2dgeq2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dmax_2dgeq2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-max-geq2"
pub fn eo__24eo_5fprog_5farith_2dmax_2dgeq2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dmax_2dgeq2(s, a0, a1);
s.leave();
result
}
pub(super) fn case_200_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmax_5fgeq2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dmax_2dgeq2(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_array-read-over-write"
pub fn eo__24eo_5fprog_5farray_2dread_2dover_2dwrite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_201_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earray_5fread_5fover_5fwrite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5farray_2dread_2dover_2dwrite(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_1_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s: &mut Store, v27: Term, a2: Term, v25: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v27, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s: &mut Store, v4: Term, v16: Term, a0: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s, v27, a2, v25)
}
pub(super) fn case_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s, v4, v16, a0, a1, a3, a2)
}
pub(super) fn body_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_array-read-over-write2"
pub fn eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_15_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5farray_2dread_2dover_2dwrite2(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_202_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earray_5fread_5fover_5fwrite2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_15_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn more_0_eo__24eo_5fprog_5farray_2dstore_2doverwrite(s: &mut Store, v11: Term, a1: Term, a3: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5farray_2dstore_2doverwrite(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farray_2dstore_2doverwrite(s, v11, a1, a3, v9)
}
pub(super) fn body_eo__24eo_5fprog_5farray_2dstore_2doverwrite(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farray_2dstore_2doverwrite(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_array-store-overwrite"
pub fn eo__24eo_5fprog_5farray_2dstore_2doverwrite(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farray_2dstore_2doverwrite(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_203_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earray_5fstore_5foverwrite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5farray_2dstore_2doverwrite(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_50_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_200_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_201_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_202_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_203_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5farray_2dstore_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5farray_2dstore_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farray_2dstore_2dself(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_array-store-self"
pub fn eo__24eo_5fprog_5farray_2dstore_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farray_2dstore_2dself(s, a0, a1);
s.leave();
result
}
pub(super) fn case_204_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earray_5fstore_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farray_2dstore_2dself(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s: &mut Store, v11: Term, a3: Term, v9: Term, a2: Term, a0: Term, a1: Term, v8: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v8, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_select, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s, v11, a3, v9, a2, a0, a1, v8)
}
pub(super) fn body_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_array-read-over-write-split"
pub fn eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_205_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earray_5fread_5fover_5fwrite_5fsplit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5farray_2dread_2dover_2dwrite_2dsplit(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_1_eo__24eo_5fprog_5farray_2dstore_2dswap(s: &mut Store, a0: Term, a2: Term, a4: Term, v27: Term, a1: Term, a3: Term, v26: Term) -> CheckResult<Option<Term>> {
let v28 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v27, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v26, v34) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v35))
}
pub(super) fn more_0_eo__24eo_5fprog_5farray_2dstore_2dswap(s: &mut Store, v4: Term, v16: Term, a0: Term, a1: Term, a3: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v17, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_store, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farray_2dstore_2dswap(s, a0, a2, a4, v27, a1, a3, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5farray_2dstore_2dswap(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
if v14 != a1 { return Ok(None); }
if v11 != a2 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farray_2dstore_2dswap(s, v4, v16, a0, a1, a3, a2, a4)
}
pub(super) fn body_eo__24eo_5fprog_5farray_2dstore_2dswap(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5farray_2dstore_2dswap(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_array-store-swap"
pub fn eo__24eo_5fprog_5farray_2dstore_2dswap(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farray_2dstore_2dswap(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_16_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5farray_2dstore_2dswap(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_206_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earray_5fstore_5fswap, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_16_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-double-not-elim"
pub fn eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_207_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fdouble_5fnot_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2ddouble_2dnot_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_51_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_204_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_205_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_206_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_207_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_12_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_48_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_49_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_50_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_51_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dnot_2dtrue(s: &mut Store, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dnot_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
if v7 != a0 { return Ok(None); }
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dnot_2dtrue(s, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dnot_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dnot_2dtrue(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-not-true"
pub fn eo__24eo_5fprog_5fbool_2dnot_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dnot_2dtrue(s, a0, a1);
s.leave();
result
}
pub(super) fn case_208_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fnot_5ftrue, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fbool_2dnot_2dtrue(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dnot_2dfalse(s: &mut Store, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dnot_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
if v7 != a0 { return Ok(None); }
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dnot_2dfalse(s, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dnot_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dnot_2dfalse(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-not-false"
pub fn eo__24eo_5fprog_5fbool_2dnot_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dnot_2dfalse(s, a0, a1);
s.leave();
result
}
pub(super) fn case_209_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fnot_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fbool_2dnot_2dfalse(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2deq_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2deq_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2deq_2dtrue(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-eq-true"
pub fn eo__24eo_5fprog_5fbool_2deq_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2deq_2dtrue(s, a0);
s.leave();
result
}
pub(super) fn case_210_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5feq_5ftrue, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2deq_2dtrue(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2deq_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2deq_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2deq_2dfalse(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-eq-false"
pub fn eo__24eo_5fprog_5fbool_2deq_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2deq_2dfalse(s, a0);
s.leave();
result
}
pub(super) fn case_211_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5feq_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2deq_2dfalse(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_52_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_208_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_209_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_210_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_211_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2deq_2dnrefl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2deq_2dnrefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2deq_2dnrefl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-eq-nrefl"
pub fn eo__24eo_5fprog_5fbool_2deq_2dnrefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2deq_2dnrefl(s, a0);
s.leave();
result
}
pub(super) fn case_212_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5feq_5fnrefl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2deq_2dnrefl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dimpl_2dfalse1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dimpl_2dfalse1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dimpl_2dfalse1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-impl-false1"
pub fn eo__24eo_5fprog_5fbool_2dimpl_2dfalse1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dimpl_2dfalse1(s, a0);
s.leave();
result
}
pub(super) fn case_213_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fimpl_5ffalse1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dimpl_2dfalse1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dimpl_2dfalse2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dimpl_2dfalse2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dimpl_2dfalse2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-impl-false2"
pub fn eo__24eo_5fprog_5fbool_2dimpl_2dfalse2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dimpl_2dfalse2(s, a0);
s.leave();
result
}
pub(super) fn case_214_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fimpl_5ffalse2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dimpl_2dfalse2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dimpl_2dtrue1(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dimpl_2dtrue1(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dimpl_2dtrue1(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-impl-true1"
pub fn eo__24eo_5fprog_5fbool_2dimpl_2dtrue1(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dimpl_2dtrue1(s, a0);
s.leave();
result
}
pub(super) fn case_215_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fimpl_5ftrue1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dimpl_2dtrue1(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_53_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_212_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_213_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_214_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_215_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dimpl_2dtrue2(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dimpl_2dtrue2(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dimpl_2dtrue2(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-impl-true2"
pub fn eo__24eo_5fprog_5fbool_2dimpl_2dtrue2(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dimpl_2dtrue2(s, a0);
s.leave();
result
}
pub(super) fn case_216_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fimpl_5ftrue2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dimpl_2dtrue2(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dimpl_2delim(s: &mut Store, v10: Term, v11: Term, v8: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v4, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dimpl_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dimpl_2delim(s, v10, v11, v8, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dimpl_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dimpl_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-impl-elim"
pub fn eo__24eo_5fprog_5fbool_2dimpl_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dimpl_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_217_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fimpl_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2dimpl_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s: &mut Store, v10: Term, v11: Term, v5: Term, v0: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v0, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s, v10, v11, v5, v0, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-dual-impl-eq"
pub fn eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s, a0, a1);
s.leave();
result
}
pub(super) fn case_218_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fdual_5fimpl_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2ddual_2dimpl_2deq(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dand_2dconf(s: &mut Store, v1: Term, a0: Term, v11: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dand_2dconf(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v4, a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v3, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dand_2dconf(s, v1, a0, v11, v0)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dand_2dconf(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dand_2dconf(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-and-conf"
pub fn eo__24eo_5fprog_5fbool_2dand_2dconf(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dand_2dconf(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_219_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fand_5fconf, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbool_2dand_2dconf(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_54_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_216_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_217_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_218_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_219_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dand_2dconf2(s: &mut Store, v1: Term, a0: Term, v11: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dand_2dconf2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v6, a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dand_2dconf2(s, v1, a0, v11, v0)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dand_2dconf2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dand_2dconf2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-and-conf2"
pub fn eo__24eo_5fprog_5fbool_2dand_2dconf2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dand_2dconf2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_220_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fand_5fconf2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbool_2dand_2dconf2(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dor_2dtaut(s: &mut Store, v1: Term, a0: Term, v11: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dor_2dtaut(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v4, a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v3, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dor_2dtaut(s, v1, a0, v11, v0)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dor_2dtaut(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dor_2dtaut(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-or-taut"
pub fn eo__24eo_5fprog_5fbool_2dor_2dtaut(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dor_2dtaut(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_221_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5for_5ftaut, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbool_2dor_2dtaut(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dor_2dtaut2(s: &mut Store, v1: Term, a0: Term, v11: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dor_2dtaut2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v6, a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dor_2dtaut2(s, v1, a0, v11, v0)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dor_2dtaut2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dor_2dtaut2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-or-taut2"
pub fn eo__24eo_5fprog_5fbool_2dor_2dtaut2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dor_2dtaut2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_222_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5for_5ftaut2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbool_2dor_2dtaut2(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s: &mut Store, v22: Term, v23: Term, v13: Term, v9: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v13, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v9, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s: &mut Store, v11: Term, a0: Term, v10: Term, a1: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListSingletonElim, &[v16, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v15, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s, v22, v23, v13, v9)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s, v11, a0, v10, a1, a2, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-or-de-morgan"
pub fn eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_223_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5for_5fde_5fmorgan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fbool_2dor_2dde_2dmorgan(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn cases_0_55_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_220_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_221_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_222_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_223_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_13_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_52_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_53_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_54_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_55_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s: &mut Store, v9: Term, v11: Term, v8: Term, v6: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v6, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s, v9, v11, v8, v6)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-implies-de-morgan"
pub fn eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s, a0, a1);
s.leave();
result
}
pub(super) fn case_224_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fimplies_5fde_5fmorgan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2dimplies_2dde_2dmorgan(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s: &mut Store, v22: Term, v23: Term, v13: Term, v9: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v13, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v9, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s: &mut Store, v11: Term, a0: Term, v10: Term, a1: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListSingletonElim, &[v16, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v15, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v14, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s, v22, v23, v13, v9)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s, v11, a0, v10, a1, a2, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-and-de-morgan"
pub fn eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_225_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fand_5fde_5fmorgan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fbool_2dand_2dde_2dmorgan(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s: &mut Store, v34: Term, v35: Term, v21: Term, v13: Term) -> CheckResult<Option<Term>> {
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v21, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v13, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s: &mut Store, a1: Term, a2: Term, v23: Term, a3: Term, a4: Term, v22: Term, v21: Term, v13: Term) -> CheckResult<Option<Term>> {
let v24 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_list(EvalOp::ListSingletonElim, &[v24, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v23, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v22, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s, v34, v35, v21, v13)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s: &mut Store, v8: Term, v11: Term, v0: Term, a0: Term, a3: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s, a1, a2, v23, a3, a4, v22, v21, v13)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a4) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s, v8, v11, v0, a0, a3, a4, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-or-and-distrib"
pub fn eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_226_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5for_5fand_5fdistrib, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v18 = match eo__24eo_5fprog_5fbool_2dor_2dand_2ddistrib(s, v2, v5, v8, v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s: &mut Store, v23: Term, a3: Term, v16: Term, v15: Term, v10: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v23, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v16, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v15, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v10, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s: &mut Store, a0: Term, a3: Term, v11: Term, a1: Term, a2: Term, v10: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListSingletonElim, &[v18, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v17, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s, v23, a3, v16, v15, v10)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s, a0, a3, v11, a1, a2, v10)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-implies-or-distrib"
pub fn eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_227_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fimplies_5for_5fdistrib, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbool_2dimplies_2dor_2ddistrib(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_56_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_224_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_225_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_226_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_227_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dxor_2drefl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dxor_2drefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dxor_2drefl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-xor-refl"
pub fn eo__24eo_5fprog_5fbool_2dxor_2drefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dxor_2drefl(s, a0);
s.leave();
result
}
pub(super) fn case_228_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fxor_5frefl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dxor_2drefl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dxor_2dnrefl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dxor_2dnrefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dxor_2dnrefl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-xor-nrefl"
pub fn eo__24eo_5fprog_5fbool_2dxor_2dnrefl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dxor_2dnrefl(s, a0);
s.leave();
result
}
pub(super) fn case_229_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fxor_5fnrefl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dxor_2dnrefl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dxor_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dxor_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dxor_2dfalse(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-xor-false"
pub fn eo__24eo_5fprog_5fbool_2dxor_2dfalse(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dxor_2dfalse(s, a0);
s.leave();
result
}
pub(super) fn case_230_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fxor_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dxor_2dfalse(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dxor_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dxor_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dxor_2dtrue(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-xor-true"
pub fn eo__24eo_5fprog_5fbool_2dxor_2dtrue(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dxor_2dtrue(s, a0);
s.leave();
result
}
pub(super) fn case_231_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fxor_5ftrue, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbool_2dxor_2dtrue(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_57_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_228_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_229_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_230_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_231_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dxor_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dxor_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dxor_2dcomm(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-xor-comm"
pub fn eo__24eo_5fprog_5fbool_2dxor_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dxor_2dcomm(s, a0, a1);
s.leave();
result
}
pub(super) fn case_232_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fxor_5fcomm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2dxor_2dcomm(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dxor_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dxor_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dxor_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-xor-elim"
pub fn eo__24eo_5fprog_5fbool_2dxor_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dxor_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_233_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fxor_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2dxor_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_xor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-not-xor-elim"
pub fn eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_234_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fnot_5fxor_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2dnot_2dxor_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s: &mut Store, v6: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v6, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s, v6, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-not-eq-elim1"
pub fn eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s, a0, a1);
s.leave();
result
}
pub(super) fn case_235_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fnot_5feq_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2dnot_2deq_2delim1(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_58_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_232_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_233_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_234_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_235_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s: &mut Store, v6: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v6, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s, v6, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-not-eq-elim2"
pub fn eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s, a0, a1);
s.leave();
result
}
pub(super) fn case_236_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fnot_5feq_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbool_2dnot_2deq_2delim2(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dneg_2dbranch(s: &mut Store, v14: Term, a0: Term, a1: Term, a2: Term, v13: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v13, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a2 { return Ok(None); }
if v4 != a1 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dneg_2dbranch(s, v14, a0, a1, a2, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dneg_2dbranch(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dneg_2dbranch(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-neg-branch"
pub fn eo__24eo_5fprog_5fite_2dneg_2dbranch(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dneg_2dbranch(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_17_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fite_2dneg_2dbranch(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_237_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fneg_5fbranch, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_17_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dthen_2dtrue(s: &mut Store, v10: Term, v11: Term, v8: Term, v6: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v6, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dthen_2dtrue(s, v10, v11, v8, v6)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dthen_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dthen_2dtrue(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-then-true"
pub fn eo__24eo_5fprog_5fite_2dthen_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dthen_2dtrue(s, a0, a1);
s.leave();
result
}
pub(super) fn case_238_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fthen_5ftrue, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2dthen_2dtrue(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2delse_2dfalse(s: &mut Store, v10: Term, v11: Term, v8: Term, v6: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v6, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2delse_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2delse_2dfalse(s, v10, v11, v8, v6)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2delse_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2delse_2dfalse(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-else-false"
pub fn eo__24eo_5fprog_5fite_2delse_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2delse_2dfalse(s, a0, a1);
s.leave();
result
}
pub(super) fn case_239_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felse_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2delse_2dfalse(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_59_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_236_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_237_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_238_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_239_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_14_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_56_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_57_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_58_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_59_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dthen_2dfalse(s: &mut Store, v11: Term, a1: Term, v10: Term, v6: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v6, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dthen_2dfalse(s, v11, a1, v10, v6)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dthen_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dthen_2dfalse(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-then-false"
pub fn eo__24eo_5fprog_5fite_2dthen_2dfalse(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dthen_2dfalse(s, a0, a1);
s.leave();
result
}
pub(super) fn case_240_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fthen_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2dthen_2dfalse(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2delse_2dtrue(s: &mut Store, v11: Term, a1: Term, v10: Term, v6: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v6, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2delse_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2delse_2dtrue(s, v11, a1, v10, v6)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2delse_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2delse_2dtrue(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-else-true"
pub fn eo__24eo_5fprog_5fite_2delse_2dtrue(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2delse_2dtrue(s, a0, a1);
s.leave();
result
}
pub(super) fn case_241_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felse_5ftrue, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2delse_2dtrue(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-then-lookahead-self"
pub fn eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself(s, a0, a1);
s.leave();
result
}
pub(super) fn case_242_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fthen_5flookahead_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dself(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-else-lookahead-self"
pub fn eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself(s, a0, a1);
s.leave();
result
}
pub(super) fn case_243_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felse_5flookahead_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2delse_2dlookahead_2dself(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_60_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_240_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_241_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_242_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_243_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s: &mut Store, v11: Term, a1: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s, v11, a1, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-then-lookahead-not-self"
pub fn eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s, a0, a1);
s.leave();
result
}
pub(super) fn case_244_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fthen_5flookahead_5fnot_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2dthen_2dlookahead_2dnot_2dself(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s: &mut Store, v10: Term, v11: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s, v10, v11, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-else-lookahead-not-self"
pub fn eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s, a0, a1);
s.leave();
result
}
pub(super) fn case_245_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felse_5flookahead_5fnot_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2delse_2dlookahead_2dnot_2dself(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_1_eo__24eo_5fprog_5fite_2dexpand(s: &mut Store, v19: Term, v23: Term, v17: Term, v16: Term, v5: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v17, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v16, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v5, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dexpand(s: &mut Store, v11: Term, a1: Term, v10: Term, v6: Term, a0: Term, a2: Term, v5: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v10, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v6, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fite_2dexpand(s, v19, v23, v17, v16, v5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dexpand(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dexpand(s, v11, a1, v10, v6, a0, a2, v5)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dexpand(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dexpand(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-expand"
pub fn eo__24eo_5fprog_5fite_2dexpand(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dexpand(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_246_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fexpand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fite_2dexpand(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s: &mut Store, v9: Term, v11: Term, a2: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v7, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s, v9, v11, a2, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bool-not-ite-elim"
pub fn eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_247_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebool_5fnot_5fite_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fbool_2dnot_2dite_2delim(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn cases_0_61_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_244_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_245_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_246_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_247_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dtrue_2dcond(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dtrue_2dcond(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-true-cond"
pub fn eo__24eo_5fprog_5fite_2dtrue_2dcond(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dtrue_2dcond(s, a0, a1);
s.leave();
result
}
pub(super) fn case_248_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5ftrue_5fcond, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2dtrue_2dcond(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dfalse_2dcond(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dfalse_2dcond(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-false-cond"
pub fn eo__24eo_5fprog_5fite_2dfalse_2dcond(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dfalse_2dcond(s, a0, a1);
s.leave();
result
}
pub(super) fn case_249_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5ffalse_5fcond, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2dfalse_2dcond(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dnot_2dcond(s: &mut Store, v7: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dnot_2dcond(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dnot_2dcond(s, v7, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dnot_2dcond(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dnot_2dcond(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-not-cond"
pub fn eo__24eo_5fprog_5fite_2dnot_2dcond(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dnot_2dcond(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_250_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fnot_5fcond, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fite_2dnot_2dcond(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2deq_2dbranch(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fite_2deq_2dbranch(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2deq_2dbranch(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-eq-branch"
pub fn eo__24eo_5fprog_5fite_2deq_2dbranch(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2deq_2dbranch(s, a0, a1);
s.leave();
result
}
pub(super) fn case_251_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5feq_5fbranch, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fite_2deq_2dbranch(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_62_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_248_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_249_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_250_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_251_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead(s: &mut Store, v11: Term, a1: Term, a3: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead(s, v11, a1, a3, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dthen_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dthen_2dlookahead(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-then-lookahead"
pub fn eo__24eo_5fprog_5fite_2dthen_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dthen_2dlookahead(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_252_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fthen_5flookahead, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fite_2dthen_2dlookahead(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2delse_2dlookahead(s: &mut Store, v11: Term, a1: Term, a3: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v3, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2delse_2dlookahead(s, v11, a1, a3, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2delse_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2delse_2dlookahead(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-else-lookahead"
pub fn eo__24eo_5fprog_5fite_2delse_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2delse_2dlookahead(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_253_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felse_5flookahead, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fite_2delse_2dlookahead(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s: &mut Store, a0: Term, a2: Term, a3: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s, a0, a2, a3, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-then-neg-lookahead"
pub fn eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_254_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5fthen_5fneg_5flookahead, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fite_2dthen_2dneg_2dlookahead(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v3, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s, a0, a1, a2, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ite-else-neg-lookahead"
pub fn eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_255_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eite_5felse_5fneg_5flookahead, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fite_2delse_2dneg_2dlookahead(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_63_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_252_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_253_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_254_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_255_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_15_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_60_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_61_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_62_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_63_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_3_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_12_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_13_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_14_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_15_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_3_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_2_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_2_1_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_2_2_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_2_3_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s: &mut Store, a6: Term, a3: Term, a1: Term, v41: Term, a2: Term, v40: Term, a0: Term, v39: Term, v38: Term) -> CheckResult<Option<Term>> {
let v42 = match s.construct(Constructor::eo_extract, &[a6, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_list(EvalOp::ListConcat, &[v40, a0, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_list(EvalOp::ListSingletonElim, &[v39, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v38, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v48))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s: &mut Store, v27: Term, v29: Term, a4: Term, a3: Term, a1: Term, a2: Term, v26: Term, a0: Term, v25: Term, a6: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v31, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v30, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_list(EvalOp::ListConcat, &[v26, a0, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v25, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s, a6, a3, a1, v41, a2, v40, a0, v39, v38)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s: &mut Store, v17: Term, v18: Term, a6: Term, a5: Term, a1: Term, a4: Term, a3: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
let v24 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s, v27, v29, a4, a3, a1, a2, v26, a0, v25, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
if v7 != a5 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a4 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s, v17, v18, a6, a5, a1, a4, a3, a2, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-concat-extract-merge"
pub fn eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn more_18_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fprog_5fbv_2dconcat_2dextract_2dmerge(s, v2, v5, v8, v11, v14, v17, v20, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn case_256_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fconcat_5fextract_5fmerge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_18_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dextract(s: &mut Store, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v48 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_extract, &[a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v48, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v53, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v56))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dextract(s: &mut Store, v28: Term, a1: Term, a3: Term, a4: Term, a2: Term, a0: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v33 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
let v36 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v39 { return Ok(None); }
if v38 != a1 { return Ok(None); }
let v40 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.unapply(v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v44 != v46 { return Ok(None); }
if v45 != a3 { return Ok(None); }
let v47 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v47 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dextract_2dextract(s, a4, a3, a2, a1, a0, a5, a6)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dextract(s: &mut Store, v17: Term, a4: Term, v18: Term, a8: Term, a6: Term, a1: Term, a3: Term, a2: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a4 { return Ok(None); }
let v23 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v23 { return Ok(None); }
let v24 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v24 else { return Ok(None); }
;
let v25 = fields[0];
let v26 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v32 { return Ok(None); }
if v31 != a6 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dextract_2dextract(s, v28, a1, a3, a4, a2, a0, a5, a6)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
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
if v7 != a5 { return Ok(None); }
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
more_0_eo__24eo_5fprog_5fbv_2dextract_2dextract(s, v17, a4, v18, a8, a6, a1, a3, a2, a0, a5)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dextract(s, a0, a1, a2, a3, a4, a5, a6, a7, a8) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-extract"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dextract(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dextract(s, a0, a1, a2, a3, a4, a5, a6, a7, a8);
s.leave();
result
}
pub(super) fn more_19_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v29 { return Ok(None); }
let v30 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__24eo_5fpf, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24eo_5fpf, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fprog_5fbv_2dextract_2dextract(s, v2, v5, v8, v11, v14, v17, v20, v31, v33) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn case_257_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fextract, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_19_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s: &mut Store, a1: Term, v30: Term, a0: Term, v29: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo_extract, &[a1, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s: &mut Store, v20: Term, v21: Term, a0: Term, v18: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a0 { return Ok(None); }
let v27 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v27 { return Ok(None); }
let v28 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v28 { return Ok(None); }
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s, a1, v30, a0, v29)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s, v20, v21, a0, v18, v4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-whole"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dwhole(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dwhole(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_258_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fwhole, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fbv_2dextract_2dwhole(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s: &mut Store, v27: Term, v28: Term, v25: Term, v23: Term, a1: Term, v22: Term, v21: Term, a4: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_list(EvalOp::ListConcat, &[v23, a1, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v22, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v21, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v36))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a4: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s, v27, v28, v25, v23, a1, v22, v21, a4, a3, a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a4 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s, v17, v19, v18, a0, v4, a4, a3, a2, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-concat-1"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_20_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d1(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_259_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fconcat_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_20_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn cases_0_64_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_256_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_257_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_258_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_259_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v95: Term, v115: Term) -> CheckResult<Option<Term>> {
let v116 = match s.apply(v95, v115) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v116))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v102: Term, v103: Term, v100: Term, a1: Term, v99: Term, v98: Term, v96: Term, a6: Term, a3: Term, a0: Term, v95: Term) -> CheckResult<Option<Term>> {
let v104 = match s.apply(v102, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.builtin_list(EvalOp::ListConcat, &[v100, a1, v104]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.builtin_list(EvalOp::ListSingletonElim, &[v99, v105]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v98, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v96, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_extract, &[a6, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v109, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v108, v114) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v95, v115)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v87: Term, v91: Term, v85: Term, a1: Term, v84: Term, v83: Term, a5: Term, a2: Term, a6: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v92 = match s.apply(v87, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.builtin_list(EvalOp::ListConcat, &[v85, a1, v92]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v84, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v83, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.construct(Constructor::eo_extract, &[a5, v97]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v102, v103, v100, a1, v99, v98, v96, a6, a3, a0, v95)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v80: Term, a0: Term, v73: Term, a4: Term, a3: Term, a2: Term, a1: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
if v80 != a0 { return Ok(None); }
let v82 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v82 { return Ok(None); }
let v83 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v86, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v89, v90) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v87, v91, v85, a1, v84, v83, a5, a2, a6, a3, a0)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v63: Term, a6: Term, a0: Term, a4: Term, a3: Term, a2: Term, a1: Term, a5: Term) -> CheckResult<Option<Term>> {
let v64 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
let v67 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
let v70 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v68 != v70 { return Ok(None); }
if v69 != a6 { return Ok(None); }
let v71 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v72, v73)) = v71 else { return Ok(None); }
;
let v74 = match s.unapply(v72) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v75, v76)) = v74 else { return Ok(None); }
;
let v77 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v75 != v77 { return Ok(None); }
let v78 = match s.unapply(v76) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v79 != v81 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v80, a0, v73, a4, a3, a2, a1, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v48: Term, v50: Term, v49: Term, a5: Term, v46: Term, a4: Term, a0: Term, a10: Term, a6: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v48 != v50 { return Ok(None); }
if v49 != a5 { return Ok(None); }
let v51 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
if v56 != a4 { return Ok(None); }
let v58 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a0 { return Ok(None); }
let v62 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v62 else { return Ok(None); }
;
let v63 = fields[0];
more_3_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v63, a6, a0, a4, a3, a2, a1, a5)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a4: Term, v32: Term, a0: Term, v25: Term, a9: Term, a5: Term, a10: Term, a6: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v34 != v36 { return Ok(None); }
if v35 != a4 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a0 { return Ok(None); }
let v41 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v41 { return Ok(None); }
let v42 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v42 else { return Ok(None); }
;
let v43 = fields[0];
let v44 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.unapply(v45) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v48, v50, v49, a5, v46, a4, a0, a10, a6, a3, a2, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a8: Term, a4: Term, a9: Term, a5: Term, a10: Term, a6: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
let v36 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v34, v36, v35, a4, v32, a0, v25, a9, a5, a10, a6, a3, a2, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a3 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v17, v19, v18, a0, v4, a8, a4, a9, a5, a10, a6, a3, a2, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-concat-2"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_22_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v42: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v37: Term, v39: Term, v41: Term) -> CheckResult<Option<Term>> {
let v43 = match s.construct(Constructor::eo__24eo_5fpf, &[v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d2(s, v2, v5, v8, v11, v14, v17, v20, v37, v39, v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v44))
}
pub(super) fn more_21_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24eo_5fcmd_5fstep_5fproven(s, v42, v2, v5, v8, v11, v14, v17, v20, v37, v39, v41)
}
pub(super) fn case_260_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fconcat_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_21_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, a1: Term, a2: Term, v74: Term, v73: Term) -> CheckResult<Option<Term>> {
let v75 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v78, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_list(EvalOp::ListConcat, &[v76, a2, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.builtin_list(EvalOp::ListSingletonElim, &[v75, v81]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v74, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v73, v83) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v84))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, a1: Term, a0: Term, a2: Term, v62: Term, v61: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v65, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.builtin_list(EvalOp::ListConcat, &[v63, a2, v70]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v62, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v61, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_extract, &[a5, a6]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, a1, a2, v74, v73)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, v48: Term, a6: Term, v45: Term, a3: Term, a0: Term, a4: Term, a1: Term, a2: Term, a5: Term) -> CheckResult<Option<Term>> {
if v48 != a6 { return Ok(None); }
let v50 = match s.unapply(v45) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
if v55 != a3 { return Ok(None); }
let v57 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v58 != v60 { return Ok(None); }
if v59 != a0 { return Ok(None); }
let v61 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, a1, a0, a2, v62, v61, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, v34: Term, v35: Term, a4: Term, v32: Term, a0: Term, a9: Term, a6: Term, a3: Term, a1: Term, a2: Term, a5: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a4 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a0 { return Ok(None); }
let v41 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v41 else { return Ok(None); }
;
let v42 = fields[0];
let v43 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v44, v45)) = v43 else { return Ok(None); }
;
let v46 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v47 != v49 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, v48, a6, v45, a3, a0, a4, a1, a2, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a8: Term, a5: Term, a4: Term, a9: Term, a6: Term, a3: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v28 != a5 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, v34, v35, a4, v32, a0, a9, a6, a3, a1, a2, a5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a3 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, v17, v19, v18, a0, v4, a8, a5, a4, a9, a6, a3, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-concat-3"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9);
s.leave();
result
}
pub(super) fn more_23_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
let v39 = match eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d3(s, v2, v5, v8, v11, v14, v17, v20, v34, v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v39))
}
pub(super) fn case_261_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fconcat_5f3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_23_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s: &mut Store, a1: Term, a2: Term, v59: Term, v58: Term) -> CheckResult<Option<Term>> {
let v60 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v63, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_list(EvalOp::ListConcat, &[v61, a2, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_list(EvalOp::ListSingletonElim, &[v60, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v59, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v58, v68) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v69))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s: &mut Store, a0: Term, a1: Term, a2: Term, v47: Term, v46: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
let v48 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v52, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_list(EvalOp::ListConcat, &[v50, a2, v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v49, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v47, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v46, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s, a1, a2, v59, v58)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s: &mut Store, v38: Term, v39: Term, a1: Term, v36: Term, a2: Term, v18: Term, a0: Term, v4: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
let v40 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a1 { return Ok(None); }
if v36 != a2 { return Ok(None); }
let v41 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a0 { return Ok(None); }
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v45 { return Ok(None); }
let v46 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s, a0, a1, a2, v47, v46, a4, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s: &mut Store, v20: Term, v21: Term, a0: Term, a1: Term, a2: Term, v18: Term, v4: Term, a4: Term, a3: Term) -> CheckResult<Option<Term>> {
let v22 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a0 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s, v38, v39, a1, v36, a2, v18, a0, v4, a4, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a4 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s, v20, v21, a0, a1, a2, v18, v4, a4, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-concat-4"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_24_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5fbv_2dextract_2dconcat_2d4(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_262_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fconcat_5f4, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_24_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, v117: Term, v118: Term, v112: Term, v110: Term, v106: Term, v104: Term) -> CheckResult<Option<Term>> {
let v119 = match s.apply(v117, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v112, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v110, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v106, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v104, v122) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v123))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, a4: Term, a5: Term, a0: Term, a1: Term, a6: Term, v106: Term, v104: Term) -> CheckResult<Option<Term>> {
let v107 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_extract, &[a4, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo_extract, &[a6, v114]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v115, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v113, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, v117, v118, v112, v110, v106, v104)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, v91: Term, v96: Term, v84: Term, a3: Term, a2: Term, a0: Term, a1: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
if v91 != v96 { return Ok(None); }
let v97 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v97 { return Ok(None); }
let v98 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_extract, &[a3, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v100, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v99, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v98, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, a4, a5, a0, a1, a6, v106, v104)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, v67: Term, v79: Term, a11: Term, a2: Term, a3: Term, a0: Term, a1: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
if v67 != v79 { return Ok(None); }
let v80 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v80 else { return Ok(None); }
;
let v81 = fields[0];
let v82 = match s.unapply(v81) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v83, v84)) = v82 else { return Ok(None); }
;
let v85 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v86 != v88 { return Ok(None); }
let v89 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v90, v91)) = v89 else { return Ok(None); }
;
let v92 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v93 != v95 { return Ok(None); }
if v94 != a2 { return Ok(None); }
let v96 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, v91, v96, v84, a3, a2, a0, a1, a4, a5, a6)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, a10: Term, a4: Term, a3: Term, a11: Term, a2: Term, a0: Term, a1: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v63 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v63 else { return Ok(None); }
;
let v64 = fields[0];
let v65 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
let v72 = match s.unapply(v70) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
let v75 = match s.unapply(v73) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v76, v77)) = v75 else { return Ok(None); }
;
let v78 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v76 != v78 { return Ok(None); }
if v77 != a4 { return Ok(None); }
if v74 != a3 { return Ok(None); }
let v79 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, v67, v79, a11, a2, a3, a0, a1, a4, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, v47: Term, a6: Term, a2: Term, a10: Term, a4: Term, a3: Term, a11: Term, a0: Term, a1: Term, a5: Term) -> CheckResult<Option<Term>> {
let v48 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
if v53 != a6 { return Ok(None); }
let v55 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a2 { return Ok(None); }
let v62 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v62 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, a10, a4, a3, a11, a2, a0, a1, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, v34: Term, v35: Term, a3: Term, v32: Term, a9: Term, a6: Term, a2: Term, a10: Term, a4: Term, a11: Term, a0: Term, a1: Term, a5: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a3 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v41 != v43 { return Ok(None); }
let v44 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
more_2_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, v47, a6, a2, a10, a4, a3, a11, a0, a1, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a8: Term, a5: Term, a3: Term, a9: Term, a6: Term, a2: Term, a10: Term, a4: Term, a11: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
if v28 != a5 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, v34, v35, a3, v32, a9, a6, a2, a10, a4, a11, a0, a1, a5)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, v17, v19, v18, a0, v11, a8, a5, a3, a9, a6, a2, a10, a4, a11, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-eq-extract-elim1"
pub fn eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term, a11: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
s.leave();
result
}
pub(super) fn more_26_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v33: Term, v36: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v40: Term, v42: Term, v44: Term) -> CheckResult<Option<Term>> {
let v45 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__24eo_5fpf, &[v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__24eo_5fpf, &[v47]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match eo__24eo_5fprog_5fbv_2deq_2dextract_2delim1(s, v2, v5, v8, v11, v14, v17, v20, v40, v42, v44, v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v49))
}
pub(super) fn more_25_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
let v38 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v38 { return Ok(None); }
let v39 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__24eo_5fpf, &[v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__24eo_5fpf, &[v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__24eo_5fpf, &[v43]) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v33, v36, v2, v5, v8, v11, v14, v17, v20, v40, v42, v44)
}
pub(super) fn case_263_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5feq_5fextract_5felim1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_25_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn cases_0_65_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_260_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_261_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_262_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_263_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, v74: Term, a0: Term, v73: Term, a1: Term, v72: Term, v70: Term) -> CheckResult<Option<Term>> {
let v75 = match s.apply(v74, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v73, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v78, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v76, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v72, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v70, v82) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v83))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, a2: Term, a0: Term, a1: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_extract, &[a2, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v64, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v63, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_extract, &[a3, a4]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, v74, a0, v73, a1, v72, v70)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, v47: Term, a3: Term, a2: Term, a0: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v48 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
let v55 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a3 { return Ok(None); }
if v57 != a2 { return Ok(None); }
let v62 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v62 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, a2, a0, a1, a3, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, v34: Term, v35: Term, a2: Term, v32: Term, a7: Term, a3: Term, a0: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a2 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v41 != v43 { return Ok(None); }
let v44 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
more_2_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, v47, a3, a2, a0, a1, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a6: Term, a4: Term, a2: Term, a7: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
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
if v28 != a4 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, v34, v35, a2, v32, a7, a3, a0, a1, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, v17, v19, v18, a0, v11, a6, a4, a2, a7, a3, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-eq-extract-elim2"
pub fn eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn more_27_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24eo_5fpf, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5fprog_5fbv_2deq_2dextract_2delim2(s, v2, v5, v8, v11, v14, v28, v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_264_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5feq_5fextract_5felim2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_27_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, v71: Term, v72: Term, v66: Term, v64: Term, v62: Term) -> CheckResult<Option<Term>> {
let v73 = match s.apply(v71, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v66, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v64, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v62, v75) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v76))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, v60: Term, a1: Term, v56: Term, a0: Term, a4: Term) -> CheckResult<Option<Term>> {
let v61 = match s.apply(v60, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v56, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_extract, &[a4, v68]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v67, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, v71, v72, v66, v64, v62)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, v51: Term, v52: Term, a2: Term, v49: Term, v42: Term, a3: Term, a0: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v53 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v53 { return Ok(None); }
if v52 != a2 { return Ok(None); }
let v54 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v54 { return Ok(None); }
let v55 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v55 { return Ok(None); }
let v56 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_extract, &[a3, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v57, v59) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, v60, a1, v56, a0, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, v34: Term, v35: Term, a2: Term, v32: Term, a7: Term, a3: Term, a0: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a2 { return Ok(None); }
let v37 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v37 { return Ok(None); }
let v38 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
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
let v47 = match s.unapply(v45) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.unapply(v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, v51, v52, a2, v49, v42, a3, a0, a1, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a6: Term, a4: Term, a2: Term, a7: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
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
if v28 != a4 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, v34, v35, a2, v32, a7, a3, a0, a1, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, v17, v19, v18, a0, v11, a6, a4, a2, a7, a3, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-eq-extract-elim3"
pub fn eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn more_28_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24eo_5fpf, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5fprog_5fbv_2deq_2dextract_2delim3(s, v2, v5, v8, v11, v14, v28, v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_265_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5feq_5fextract_5felim3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_28_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dnot(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_extract, &[a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_extract, &[a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dnot(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dnot(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-not"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dnot(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dnot(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_266_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fbv_2dextract_2dnot(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s: &mut Store, v26: Term, v28: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_extract, &[a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v21, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_extract, &[a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s, v26, v28)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v14 != a2 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s, v17, v19, v18, a0, v4, a2, a1, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-sign-extend-1"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_29_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d1(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_267_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_29_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_66_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_264_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_265_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_266_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_267_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, v105: Term, v107: Term, v104: Term) -> CheckResult<Option<Term>> {
let v108 = match s.apply(v105, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v104, v108) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v109))
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, v96: Term, a0: Term, v82: Term, a2: Term, a1: Term, a3: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
if v96 != a0 { return Ok(None); }
let v98 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v82 != v98 { return Ok(None); }
let v99 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_extract, &[a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v100, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v99, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_sign_5fextend, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_extract, &[a4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, v105, v107, v104)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, v74: Term, a2: Term, a0: Term, a1: Term, a3: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v80 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.unapply(v81) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v86 { return Ok(None); }
let v87 = match s.unapply(v85) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v88, v89)) = v87 else { return Ok(None); }
;
let v90 = match s.unapply(v88) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v91 != v93 { return Ok(None); }
if v92 != a2 { return Ok(None); }
let v94 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v95, v96)) = v94 else { return Ok(None); }
;
let v97 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v95 != v97 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, v96, a0, v82, a2, a1, a3, a5, a4)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, a9: Term, a5: Term, a2: Term, a0: Term, a1: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v63 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v63 else { return Ok(None); }
;
let v64 = fields[0];
let v65 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a5 { return Ok(None); }
let v72 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
let v75 = match s.unapply(v73) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v76, v77)) = v75 else { return Ok(None); }
;
let v78 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v76 != v78 { return Ok(None); }
let v79 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v77 != v79 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, v74, a2, a0, a1, a3, a5, a4)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, v48: Term, v50: Term, v49: Term, a4: Term, v46: Term, a0: Term, a9: Term, a5: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v48 != v50 { return Ok(None); }
if v49 != a4 { return Ok(None); }
let v51 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.unapply(v52) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v55 != v57 { return Ok(None); }
let v58 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v61 { return Ok(None); }
if v60 != a0 { return Ok(None); }
let v62 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v62 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, a9, a5, a2, a0, a1, a3, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, v34: Term, v36: Term, v35: Term, a2: Term, v32: Term, a0: Term, v25: Term, a8: Term, a4: Term, a9: Term, a5: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v34 != v36 { return Ok(None); }
if v35 != a2 { return Ok(None); }
let v37 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a0 { return Ok(None); }
let v41 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v41 { return Ok(None); }
let v42 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v42 else { return Ok(None); }
;
let v43 = fields[0];
let v44 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.unapply(v45) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, v48, v50, v49, a4, v46, a0, a9, a5, a2, a1, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a7: Term, a2: Term, a8: Term, a4: Term, a9: Term, a5: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
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
let v36 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, v34, v36, v35, a2, v32, a0, v25, a8, a4, a9, a5, a1, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, v17, v19, v18, a0, v4, a7, a2, a8, a4, a9, a5, a1, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-sign-extend-2"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9);
s.leave();
result
}
pub(super) fn more_31_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v34: Term, v36: Term, v38: Term, v40: Term) -> CheckResult<Option<Term>> {
let v41 = match eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d2(s, v2, v5, v8, v11, v14, v17, v34, v36, v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_30_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
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
let v33 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__24eo_5fpf, &[v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__24eo_5fpf, &[v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__24eo_5fpf, &[v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__24eo_5fpf, &[v39]) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v11, v14, v17, v34, v36, v38, v40)
}
pub(super) fn case_268_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_30_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v21, v24, v2, v5, v8, v11, v14, v17)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, v75: Term, v77: Term, v74: Term, a4: Term, a5: Term, a0: Term) -> CheckResult<Option<Term>> {
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_repeat, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_extract, &[a5, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v80, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v79, v83) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v84))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, v66: Term, v67: Term, a0: Term, v64: Term, a2: Term, a1: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v68 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v66 != v68 { return Ok(None); }
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
if v71 != a0 { return Ok(None); }
let v73 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v64 != v73 { return Ok(None); }
let v74 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_extract, &[a2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, v75, v77, v74, a4, a5, a0)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, v50: Term, a2: Term, v47: Term, a1: Term, v40: Term, a8: Term, a5: Term, a0: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
if v50 != a2 { return Ok(None); }
if v47 != a1 { return Ok(None); }
let v52 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v52 { return Ok(None); }
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
if v60 != a5 { return Ok(None); }
let v62 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, v66, v67, a0, v64, a2, a1, a3, a4, a5)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, v34: Term, v35: Term, v32: Term, a2: Term, a1: Term, a8: Term, a5: Term, a0: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
let v37 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
let v38 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
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
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, v50, a2, v47, a1, v40, a8, a5, a0, a3, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a7: Term, a4: Term, a2: Term, a1: Term, a8: Term, a5: Term, a3: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
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
if v28 != a4 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, v34, v35, v32, a2, a1, a8, a5, a0, a3, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, v17, v19, v18, a0, v4, a7, a4, a2, a1, a8, a5, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-extract-sign-extend-3"
pub fn eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, a0, a1, a2, a3, a4, a5, a6, a7, a8);
s.leave();
result
}
pub(super) fn more_32_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
let v26 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = fields[1];
let v29 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v29 { return Ok(None); }
let v30 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__24eo_5fpf, &[v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24eo_5fpf, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__24eo_5fpf, &[v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5fprog_5fbv_2dextract_2dsign_2dextend_2d3(s, v2, v5, v8, v11, v14, v17, v31, v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v36))
}
pub(super) fn case_269_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fextract_5fsign_5fextend_5f3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_32_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v21, v24, v2, v5, v8, v11, v14, v17)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dnot_2dxor(s: &mut Store, v11: Term, a0: Term, v10: Term, a1: Term, a2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v9, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dnot_2dxor(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v0, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dnot_2dxor(s, v11, a0, v10, a1, a2, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dnot_2dxor(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dnot_2dxor(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-not-xor"
pub fn eo__24eo_5fprog_5fbv_2dnot_2dxor(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dnot_2dxor(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_270_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fnot_5fxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fbv_2dnot_2dxor(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s: &mut Store, a4: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s: &mut Store, a3: Term, a2: Term, a1: Term, v14: Term, a0: Term, v13: Term, a4: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v19, a1, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListConcat, &[v14, a0, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v13, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s, a4, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a3 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s, a3, a2, a1, v14, a0, v13, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-and-simplify-1"
pub fn eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_33_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d1(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_271_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fand_5fsimplify_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_33_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn cases_0_67_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_268_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_269_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_270_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_271_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_16_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_64_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_65_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_66_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_67_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s: &mut Store, a4: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s: &mut Store, a3: Term, a2: Term, a1: Term, v14: Term, a0: Term, v13: Term, a4: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v17, a1, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v16, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListConcat, &[v14, a0, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v13, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s, a4, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a3 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s, a3, a2, a1, v14, a0, v13, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-and-simplify-2"
pub fn eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_34_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5fbv_2dand_2dsimplify_2d2(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_272_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fand_5fsimplify_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_34_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s: &mut Store, a4: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v27, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v26, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s: &mut Store, a3: Term, a2: Term, a1: Term, v14: Term, a0: Term, v13: Term, a4: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v19, a1, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListConcat, &[v14, a0, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v13, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s, a4, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a3 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s, a3, a2, a1, v14, a0, v13, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-or-simplify-1"
pub fn eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_35_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d1(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_273_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5for_5fsimplify_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_35_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s: &mut Store, a4: Term, v26: Term) -> CheckResult<Option<Term>> {
let v27 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v27, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v26, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s: &mut Store, a3: Term, a2: Term, a1: Term, v14: Term, a0: Term, v13: Term, a4: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v17, a1, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v16, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListConcat, &[v14, a0, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v13, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s, a4, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a3 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s, a3, a2, a1, v14, a0, v13, a4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-or-simplify-2"
pub fn eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_36_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fprog_5fbv_2dor_2dsimplify_2d2(s, v2, v5, v8, v11, v14, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_274_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5for_5fsimplify_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_36_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v18, v2, v5, v8, v11, v14)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s: &mut Store, a1: Term, a2: Term, a0: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListConcat, &[v14, a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListConcat, &[v13, a0, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListSingletonElim, &[v12, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListConcat, &[v4, a1, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v3, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v0, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s, a1, a2, a0, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-simplify-1"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_275_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d1(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn cases_0_68_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_272_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_273_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_274_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_275_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s: &mut Store, v1: Term, a0: Term, v11: Term, v0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListConcat, &[v17, a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListConcat, &[v16, a0, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListSingletonElim, &[v15, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v13, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v4, a1, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v3, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s, v1, a0, v11, v0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-simplify-2"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_276_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d2(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s: &mut Store, v1: Term, a0: Term, v11: Term, v0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_list(EvalOp::ListConcat, &[v1, a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListConcat, &[v17, a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListConcat, &[v16, a0, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListSingletonElim, &[v15, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v13, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v6, a1, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s, v1, a0, v11, v0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-xor-simplify-3"
pub fn eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_277_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fxor_5fsimplify_5f3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fbv_2dxor_2dsimplify_2d3(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, v53: Term, v66: Term, v37: Term) -> CheckResult<Option<Term>> {
let v67 = match s.apply(v53, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v37, v67) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v68))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, a1: Term, a2: Term, a0: Term, v54: Term, v53: Term, v37: Term) -> CheckResult<Option<Term>> {
let v55 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_list(EvalOp::ListConcat, &[v58, a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_list(EvalOp::ListSingletonElim, &[v57, v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v56, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v55, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v54, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v64, v65) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, v53, v66, v37)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, v42: Term, a1: Term, a2: Term, v41: Term, v40: Term, a4: Term, v39: Term, v38: Term, a0: Term, v37: Term) -> CheckResult<Option<Term>> {
let v43 = match s.builtin_list(EvalOp::ListConcat, &[v42, a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_list(EvalOp::ListSingletonElim, &[v41, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v40, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v46, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v45, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v39, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v38, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, a1, a2, a0, v54, v53, v37)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, a3: Term, a2: Term, a1: Term, v30: Term, v28: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
let v31 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_list(EvalOp::ListConcat, &[v31, a1, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v30, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v28, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, v42, a1, a2, v41, v40, a4, v39, v38, a0, v37)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, v16: Term, a4: Term, a0: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a4 { return Ok(None); }
let v24 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
if v26 != a0 { return Ok(None); }
let v28 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, a3, a2, a1, v30, v28, a4, a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
if v7 != a3 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.destruct(Constructor::eo_int_5fto_5fbv, v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v12 else { return Ok(None); }
;
let v13 = fields[0];
if v13 != a4 { return Ok(None); }
let v14 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v14 { return Ok(None); }
let v15 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v15 else { return Ok(None); }
;
let v16 = fields[0];
more_0_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, v16, a4, a0, a3, a2, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ult-add-one"
pub fn eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn more_37_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fprog_5fbv_2dult_2dadd_2done(s, v2, v5, v8, v11, v14, v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_278_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fult_5fadd_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_37_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v18, v21, v2, v5, v8, v11, v14)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, v117: Term, v133: Term, v107: Term, v94: Term) -> CheckResult<Option<Term>> {
let v134 = match s.apply(v117, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v107, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v94, v135) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v136))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, v121: Term, a0: Term, v119: Term, a2: Term, a6: Term, v118: Term, v117: Term, v107: Term, v94: Term) -> CheckResult<Option<Term>> {
let v122 = match s.apply(v121, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v119, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_bvsgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v126, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v125, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v123, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v118, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v131, v132) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, v117, v133, v107, v94)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, a2: Term, a6: Term, v109: Term, v108: Term, a1: Term, a0: Term, v107: Term, v94: Term) -> CheckResult<Option<Term>> {
let v110 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v111, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v109, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v108, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, v121, a0, v119, a2, a6, v118, v117, v107, v94)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, a1: Term, a0: Term, v97: Term, a5: Term, v96: Term, v95: Term, a2: Term, a6: Term, v94: Term) -> CheckResult<Option<Term>> {
let v98 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v98, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v97, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v102, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v101, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v96, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v95, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, a2, a6, v109, v108, a1, a0, v107, v94)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, a3: Term, a0: Term, v85: Term, v81: Term, v77: Term, v60: Term, a1: Term, a5: Term, a2: Term, a6: Term) -> CheckResult<Option<Term>> {
let v86 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match eo__24eo_5ftypeof(s, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match eo__24eo_5fnil(s, v86, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v85, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v81, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v77, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v60, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, a1, a0, v97, a5, v96, v95, a2, a6, v94)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, v70: Term, v73: Term, v69: Term, v65: Term, v61: Term, a3: Term, a0: Term, a4: Term, a2: Term, v60: Term, a1: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v74 = match eo__24eo_5fnil(s, v70, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v69, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v65, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v61, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_sign_5fextend, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v82, v84) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, a3, a0, v85, v81, v77, v60, a1, a5, a2, a6)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, a3: Term, a1: Term, a4: Term, a2: Term, v61: Term, a0: Term, v60: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v62 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_sign_5fextend, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v66, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, v70, v73, v69, v65, v61, a3, a0, a4, a2, v60, a1, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, v49: Term, v50: Term, a4: Term, a6: Term, v47: Term, a3: Term, a1: Term, a2: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v56 != v58 { return Ok(None); }
if v57 != a4 { return Ok(None); }
if v54 != a6 { return Ok(None); }
let v59 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v47 != v59 { return Ok(None); }
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, a3, a1, a4, a2, v61, a0, v60, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, v32: Term, v34: Term, v33: Term, a3: Term, a5: Term, v30: Term, a10: Term, a4: Term, a6: Term, a1: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
if v32 != v34 { return Ok(None); }
let v35 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
if v40 != a3 { return Ok(None); }
if v37 != a5 { return Ok(None); }
let v42 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v42 { return Ok(None); }
let v43 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v43 else { return Ok(None); }
;
let v44 = fields[0];
let v45 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, v49, v50, a4, a6, v47, a3, a1, a2, a0, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, v16: Term, a6: Term, v17: Term, a2: Term, a9: Term, a3: Term, a5: Term, a10: Term, a4: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != a6 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
if v24 != a2 { return Ok(None); }
let v26 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, v32, v34, v33, a3, a5, v30, a10, a4, a6, a1, a2, a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
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
if v7 != a5 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, v16, a6, v17, a2, a9, a3, a5, a10, a4, a1, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-mult-slt-mult-1"
pub fn eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_39_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v42: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v37: Term, v39: Term, v41: Term) -> CheckResult<Option<Term>> {
let v43 = match s.construct(Constructor::eo__24eo_5fpf, &[v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d1(s, v2, v5, v8, v11, v14, v17, v20, v37, v39, v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v44))
}
pub(super) fn more_38_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
more_39_eo__24eo_5fcmd_5fstep_5fproven(s, v42, v2, v5, v8, v11, v14, v17, v20, v37, v39, v41)
}
pub(super) fn case_279_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_38_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn cases_0_69_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_276_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_277_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_278_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_279_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, v117: Term, v133: Term, v107: Term, v94: Term) -> CheckResult<Option<Term>> {
let v134 = match s.apply(v117, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v107, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v94, v135) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v136))
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, v121: Term, a0: Term, v119: Term, a2: Term, a6: Term, v118: Term, v117: Term, v107: Term, v94: Term) -> CheckResult<Option<Term>> {
let v122 = match s.apply(v121, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v119, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_bvsgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v124, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v126, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v125, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v123, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v118, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v131, v132) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, v117, v133, v107, v94)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, a2: Term, a6: Term, v109: Term, v108: Term, a1: Term, a0: Term, v107: Term, v94: Term) -> CheckResult<Option<Term>> {
let v110 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a6]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v111, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v109, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v108, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, v121, a0, v119, a2, a6, v118, v117, v107, v94)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, a1: Term, a0: Term, v97: Term, a5: Term, v96: Term, v95: Term, a2: Term, a6: Term, v94: Term) -> CheckResult<Option<Term>> {
let v98 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v98, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v97, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v102, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v101, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v96, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v95, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, a2, a6, v109, v108, a1, a0, v107, v94)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, a3: Term, a0: Term, v85: Term, v81: Term, v77: Term, v60: Term, a1: Term, a5: Term, a2: Term, a6: Term) -> CheckResult<Option<Term>> {
let v86 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_zero_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match eo__24eo_5ftypeof(s, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match eo__24eo_5fnil(s, v86, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v85, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v81, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v77, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v60, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, a1, a0, v97, a5, v96, v95, a2, a6, v94)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, v70: Term, v73: Term, v69: Term, v65: Term, v61: Term, a3: Term, a0: Term, a4: Term, a2: Term, v60: Term, a1: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v74 = match eo__24eo_5fnil(s, v70, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v69, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v65, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v61, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_zero_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_sign_5fextend, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v83, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v82, v84) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, a3, a0, v85, v81, v77, v60, a1, a5, a2, a6)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, a3: Term, a1: Term, a4: Term, a2: Term, v61: Term, a0: Term, v60: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v62 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_zero_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_sign_5fextend, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v66, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_bvmul, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_zero_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v71, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24eo_5ftypeof(s, v72) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, v70, v73, v69, v65, v61, a3, a0, a4, a2, v60, a1, a5, a6)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, v49: Term, v50: Term, a4: Term, a6: Term, v47: Term, a3: Term, a1: Term, a2: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v56 != v58 { return Ok(None); }
if v57 != a4 { return Ok(None); }
if v54 != a6 { return Ok(None); }
let v59 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v47 != v59 { return Ok(None); }
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, a3, a1, a4, a2, v61, a0, v60, a5, a6)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, v32: Term, v34: Term, v33: Term, a3: Term, a5: Term, v30: Term, a10: Term, a4: Term, a6: Term, a1: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
if v32 != v34 { return Ok(None); }
let v35 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
if v40 != a3 { return Ok(None); }
if v37 != a5 { return Ok(None); }
let v42 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v30 != v42 { return Ok(None); }
let v43 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v43 else { return Ok(None); }
;
let v44 = fields[0];
let v45 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, v49, v50, a4, a6, v47, a3, a1, a2, a0, a5)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, v16: Term, a6: Term, v17: Term, a2: Term, a9: Term, a3: Term, a5: Term, a10: Term, a4: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != a6 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
if v24 != a2 { return Ok(None); }
let v26 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
let v28 = match s.unapply(v27) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, v32, v34, v33, a3, a5, v30, a10, a4, a6, a1, a2, a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Option<Term>> {
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
if v7 != a5 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, v16, a6, v17, a2, a9, a3, a5, a10, a4, a1, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-mult-slt-mult-2"
pub fn eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term, a10: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10);
s.leave();
result
}
pub(super) fn more_41_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v42: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v37: Term, v39: Term, v41: Term) -> CheckResult<Option<Term>> {
let v43 = match s.construct(Constructor::eo__24eo_5fpf, &[v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24eo_5fprog_5fbv_2dmult_2dslt_2dmult_2d2(s, v2, v5, v8, v11, v14, v17, v20, v37, v39, v41, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v44))
}
pub(super) fn more_40_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
let v32 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = fields[1];
let v35 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v35 { return Ok(None); }
let v36 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24eo_5fpf, &[v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fpf, &[v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__24eo_5fpf, &[v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v33) { Ok(v) => v, Err(e) => return Err(e) };
more_41_eo__24eo_5fcmd_5fstep_5fproven(s, v42, v2, v5, v8, v11, v14, v17, v20, v37, v39, v41)
}
pub(super) fn case_280_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fmult_5fslt_5fmult_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_40_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s: &mut Store, v11: Term, a1: Term, a0: Term, v10: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5fnil(s, v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v10, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fnil(s, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s, v11, a1, a0, v10)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-commutative-xor"
pub fn eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s, a0, a1);
s.leave();
result
}
pub(super) fn case_281_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fcommutative_5fxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dcommutative_2dxor(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dcommutative_2dcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dcommutative_2dcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dcommutative_2dcomp(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-commutative-comp"
pub fn eo__24eo_5fprog_5fbv_2dcommutative_2dcomp(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dcommutative_2dcomp(s, a0, a1);
s.leave();
result
}
pub(super) fn case_282_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fcommutative_5fcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dcommutative_2dcomp(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_zero_5fextend, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-zero-extend-eliminate-0"
pub fn eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0(s, a0);
s.leave();
result
}
pub(super) fn case_283_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fzero_5fextend_5feliminate_5f0, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2deliminate_2d0(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_70_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_280_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_281_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_282_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_283_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_sign_5fextend, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sign-extend-eliminate-0"
pub fn eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0(s, a0);
s.leave();
result
}
pub(super) fn case_284_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsign_5fextend_5feliminate_5f0, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dsign_2dextend_2deliminate_2d0(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dnot_2dneq(s: &mut Store, v28: Term) -> CheckResult<Option<Term>> {
let v29 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dnot_2dneq(s: &mut Store, v18: Term, a0: Term, v11: Term, v4: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v22, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dnot_2dneq(s, v28)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dnot_2dneq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dnot_2dneq(s, v18, a0, v11, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dnot_2dneq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dnot_2dneq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-not-neq"
pub fn eo__24eo_5fprog_5fbv_2dnot_2dneq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dnot_2dneq(s, a0, a1);
s.leave();
result
}
pub(super) fn case_285_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fnot_5fneq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5fbv_2dnot_2dneq(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dult_2dones(s: &mut Store, v27: Term, v40: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v27, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dult_2dones(s: &mut Store, a0: Term, a2: Term, a1: Term, v28: Term, v27: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v31, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24eo_5fnil(s, v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v34, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v30, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v28, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dult_2dones(s, v27, v40)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dult_2dones(s: &mut Store, v17: Term, v19: Term, v18: Term, a2: Term, v11: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a2 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v21, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_distinct, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dult_2dones(s, a0, a2, a1, v28, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dult_2dones(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v19 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dult_2dones(s, v17, v19, v18, a2, v11, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dult_2dones(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dult_2dones(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ult-ones"
pub fn eo__24eo_5fprog_5fbv_2dult_2dones(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dult_2dones(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_42_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2dult_2dones(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_286_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fult_5fones, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_42_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, v39: Term, a0: Term, v65: Term, v38: Term, v37: Term) -> CheckResult<Option<Term>> {
let v66 = match s.builtin_list(EvalOp::ListConcat, &[v39, a0, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_list(EvalOp::ListSingletonElim, &[v38, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v37, v67) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v68))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, a3: Term, a4: Term, v53: Term, v52: Term, v41: Term, v40: Term, a6: Term, v39: Term, a0: Term, v38: Term, v37: Term) -> CheckResult<Option<Term>> {
let v54 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v53, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v59, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v52, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v41, v62) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v40, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, a6) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, v39, a0, v65, v38, v37)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, a1: Term, a4: Term, a3: Term, v41: Term, v40: Term, a6: Term, v39: Term, a0: Term, v38: Term, v37: Term) -> CheckResult<Option<Term>> {
let v42 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v48, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v42, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, a3, a4, v53, v52, v41, v40, a6, v39, a0, v38, v37)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, a4: Term, a3: Term, a6: Term, v29: Term, v25: Term, a0: Term, v24: Term, a5: Term, a1: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a6) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v29, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_list(EvalOp::ListConcat, &[v25, a0, v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v24, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, a1, a4, a3, v41, v40, a6, v39, a0, v38, v37)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, v17: Term, a4: Term, v18: Term, a2: Term, a1: Term, a3: Term, a6: Term, a0: Term, a5: Term) -> CheckResult<Option<Term>> {
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a4 { return Ok(None); }
let v23 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v23 { return Ok(None); }
let v24 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, a4, a3, a6, v29, v25, a0, v24, a5, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
if v7 != a5 { return Ok(None); }
let v9 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.unapply(v10) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a2 { return Ok(None); }
let v16 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, v17, a4, v18, a2, a1, a3, a6, a0, a5)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-concat-merge-const"
pub fn eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn more_43_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fprog_5fbv_2dconcat_2dmerge_2dconst(s, v2, v5, v8, v11, v14, v17, v20, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn case_287_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fconcat_5fmerge_5fconst, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
more_43_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn cases_0_71_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_284_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_285_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_286_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_287_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_17_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_68_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_69_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_70_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_71_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s: &mut Store, v11: Term, a1: Term, a0: Term, v10: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5fnil(s, v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v10, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5fnil(s, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v0, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s, v11, a1, a0, v10)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-commutative-add"
pub fn eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s, a0, a1);
s.leave();
result
}
pub(super) fn case_288_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fcommutative_5fadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dcommutative_2dadd(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate(s: &mut Store, a0: Term, v11: Term, v10: Term, v6: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fnil(s, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v6, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvsub, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_bvadd, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate(s, a0, v11, v10, v6, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsub_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsub_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sub-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsub_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsub_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_289_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsub_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dsub_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s: &mut Store, v11: Term, v9: Term, v0: Term, a0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v0, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v3, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s, v11, v9, v0, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-width-one"
pub fn eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s, a0);
s.leave();
result
}
pub(super) fn case_290_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fwidth_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dite_2dwidth_2done(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s: &mut Store, v11: Term, v9: Term, v0: Term, a0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v0, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v20, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v3, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v1, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s, v11, v9, v0, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ite-width-one-not"
pub fn eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s, a0);
s.leave();
result
}
pub(super) fn case_291_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fite_5fwidth_5fone_5fnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbv_2dite_2dwidth_2done_2dnot(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_72_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_288_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_289_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_290_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_291_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s: &mut Store, v20: Term, v23: Term, v18: Term, v16: Term, v14: Term, v0: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v18, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v16, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v14, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v0, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s: &mut Store, v2: Term, v11: Term, a2: Term, v1: Term, a0: Term, a1: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v2, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v1, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5ftypeof(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fnil(s, v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s, v20, v23, v18, v16, v14, v0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_bvxor, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fnil(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s, v2, v11, a2, v1, a0, a1, v0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-eq-xor-solve"
pub fn eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_292_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5feq_5fxor_5fsolve, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fbv_2deq_2dxor_2dsolve(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s: &mut Store, v9: Term, v11: Term, v7: Term, v0: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v0, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v1, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s, v9, v11, v7, v0)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-eq-not-solve"
pub fn eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s, a0, a1);
s.leave();
result
}
pub(super) fn case_293_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5feq_5fnot_5fsolve, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2deq_2dnot_2dsolve(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dugt_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvugt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dugt_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dugt_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-ugt-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dugt_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dugt_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_294_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fugt_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dugt_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvuge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2duge_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2duge_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-uge-eliminate"
pub fn eo__24eo_5fprog_5fbv_2duge_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2duge_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_295_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fuge_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2duge_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_73_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_292_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_293_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_294_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_295_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsgt_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvsgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsgt_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsgt_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sgt-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsgt_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsgt_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_296_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsgt_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dsgt_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsge_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvsge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_bvsle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsge_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsge_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sge-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsge_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsge_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_297_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsge_5feliminate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fbv_2dsge_2deliminate(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsle_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvsle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_bvslt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsle_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsle_2deliminate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sle-eliminate"
pub fn eo__24eo_5fprog_5fbv_2dsle_2deliminate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsle_2deliminate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_298_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v21 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v16, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
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
pub(super) fn case_299_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_74_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_296_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_297_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_298_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_299_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dredand_2deliminate(s: &mut Store, v14: Term, a0: Term, v13: Term, a1: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_bvcomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v16, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
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
pub(super) fn case_300_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_301_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s: &mut Store, v11: Term, v9: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v4, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
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
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dcomp_2deliminate(s, v11, v9, v4)
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
pub(super) fn case_302_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v137: Term, v139: Term, v136: Term, v131: Term) -> CheckResult<Option<Term>> {
let v140 = match s.apply(v137, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v140, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v136, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v131, v143) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v144))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, a1: Term, a0: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v128 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_rotate_5fleft, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v129, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v128, v130) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_extract, &[a2, v133]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v134, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v132, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_extract, &[a3, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v138, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v137, v139, v136, v131)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v114: Term, v115: Term, a0: Term, v108: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v116 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v114 != v116 { return Ok(None); }
if v115 != a0 { return Ok(None); }
let v117 = match s.unapply(v108) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v118, v119)) = v117 else { return Ok(None); }
;
let v120 = match s.unapply(v118) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v121, v122)) = v120 else { return Ok(None); }
;
let v123 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v121 != v123 { return Ok(None); }
if v122 != a1 { return Ok(None); }
let v124 = match s.unapply(v119) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v125, v126)) = v124 else { return Ok(None); }
;
let v127 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v125 != v127 { return Ok(None); }
if v126 != a0 { return Ok(None); }
more_7_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, a1, a0, a2, a3, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v87: Term, v96: Term, a8: Term, a4: Term, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if v87 != v96 { return Ok(None); }
let v97 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v97 else { return Ok(None); }
;
let v98 = fields[0];
let v99 = match s.unapply(v98) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v100, v101)) = v99 else { return Ok(None); }
;
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v103 != v105 { return Ok(None); }
if v104 != a4 { return Ok(None); }
let v106 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.unapply(v107) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v110, v111)) = v109 else { return Ok(None); }
;
let v112 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v110 != v112 { return Ok(None); }
let v113 = match s.unapply(v111) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
more_6_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v114, v115, a0, v108, a1, a2, a3, a4)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v82: Term, v83: Term, a3: Term, v80: Term, a0: Term, a8: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v84 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v82 != v84 { return Ok(None); }
if v83 != a3 { return Ok(None); }
let v85 = match s.unapply(v80) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v89 != v91 { return Ok(None); }
let v92 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v93 != v95 { return Ok(None); }
if v94 != a0 { return Ok(None); }
let v96 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v87, v96, a8, a4, a0, a1, a2, a3)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v68: Term, v69: Term, a1: Term, v66: Term, a0: Term, v59: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
let v70 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v68 != v70 { return Ok(None); }
if v69 != a1 { return Ok(None); }
let v71 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v72, v73)) = v71 else { return Ok(None); }
;
let v74 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v72 != v74 { return Ok(None); }
if v73 != a0 { return Ok(None); }
let v75 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v75 { return Ok(None); }
let v76 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v76 else { return Ok(None); }
;
let v77 = fields[0];
let v78 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
let v81 = match s.unapply(v79) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v82, v83)) = v81 else { return Ok(None); }
;
more_4_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v82, v83, a3, v80, a0, a8, a4, a1, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v40: Term, a1: Term, a0: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term) -> CheckResult<Option<Term>> {
let v49 = match s.unapply(v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
let v56 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
let v57 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v61 != v63 { return Ok(None); }
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
let v67 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v68, v69, a1, v66, a0, v59, a7, a3, a8, a4, a2)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s: &mut Store, v32: Term, a2: Term, v33: Term, a0: Term, a1: Term, a7: Term, a3: Term, a8: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v48 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != a0 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v40, a1, a0, a7, a3, a8, a4, a2)
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
more_1_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d1(s, v32, a2, v33, a0, a1, a7, a3, a8, a4)
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
pub(super) fn case_303_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2drotate_2dleft_2deliminate_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_rotate_5fleft, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
