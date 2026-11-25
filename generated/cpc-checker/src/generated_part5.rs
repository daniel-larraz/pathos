//! Generated functions, module 5 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn body_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s, a0, a1, a2) {
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
// EO program "$str_mk_str_in_re_sigma_star_rec"
pub fn eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1075), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1075), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s: &mut Store, v12: Term, v16: Term, v18: Term, v2: Term) -> CheckResult<Option<Term>> {
let v19 = match eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s, v12, v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s, v19, v2, v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s, v12, v16, v18, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-sigma-star"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s, a0);
s.leave();
result
}
pub(super) fn case_119_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5fsigma_5fstar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_29_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_116_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_117_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_118_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_119_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s: &mut Store, v22: Term, v23: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v22 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
pub(super) fn if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, condition: Term, v5: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
Ok(a2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListErase, &[v7, a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListErase, &[v9, a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Eq, &[a1, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, v11, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v8, v15])))
}
pub(super) fn if_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, condition: Term, a0: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
Ok(a2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$str_is_multiset_subset_strict_done"
pub fn eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1066), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1066), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24str_5fvalue_5flen(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsEq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24are_5fdistinct_5fterms_5flist_5frec(s, v5, a0, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::And, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s, v12, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn if_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, condition: Term, a1: Term, a2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_list(EvalOp::ListErase, &[v2, a1, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListErase, &[v4, a1, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Eq, &[a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, v6, a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5fis_5fmultiset_5fsubset_5fstrict_5fdone(s, v3, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_2_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, v0, a1, a2, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v12)))
}
pub(super) fn step_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, a0, a1, a2) {
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
// EO program "$str_is_multiset_subset_strict"
pub fn eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1065), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1065), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24str_5fmultiset_5foverapprox(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
Ok(Some(Next::Again([v8])))
}
pub(super) fn if_0_eo__24str_5fmultiset_5foverapprox_5fword(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fnil(s, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5fmultiset_5foverapprox_5fword(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24str_5fmultiset_5foverapprox_5fword(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
// EO program "$str_multiset_overapprox_word"
pub fn eo__24str_5fmultiset_5foverapprox_5fword(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1077), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fmultiset_5foverapprox_5fword(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1077), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fmultiset_5foverapprox_5fword(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fmultiset_5foverapprox_5fword(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmultiset_5foverapprox_5fword(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fmultiset_5foverapprox_5fword(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24str_5fmultiset_5foverapprox_5fword(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn if_0_eo__24str_5fmultiset_5foverapprox(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v5, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24str_5fflatten(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24str_5fmultiset_5foverapprox_5fword(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fnil(s, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5fmultiset_5foverapprox(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
let v4 = match s.builtin_core(EvalOp::IsStr, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_0_eo__24str_5fmultiset_5foverapprox(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_3_eo__24str_5fmultiset_5foverapprox(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match eo__24str_5fis_5fempty(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_1_eo__24str_5fmultiset_5foverapprox(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v16)))
}
// EO program "$str_multiset_overapprox"
pub fn eo__24str_5fmultiset_5foverapprox(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1076), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fmultiset_5foverapprox(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1076), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fmultiset_5foverapprox(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fmultiset_5foverapprox(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24str_5fmultiset_5foverapprox(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fmultiset_5foverapprox(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmultiset_5foverapprox(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fmultiset_5foverapprox(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24str_5fmultiset_5foverapprox(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_0_eo__24str_5fmultiset_5foverapprox(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24str_5fmultiset_5foverapprox(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24str_5fmultiset_5foverapprox(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v7, v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_2_eo__24str_5fmultiset_5foverapprox(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
let v10 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5fmultiset_5foverapprox(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24str_5fmultiset_5foverapprox(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListConcat, &[v10, v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v13)))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s: &mut Store, v16: Term, v12: Term, v9: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24str_5fflatten(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24str_5fmultiset_5foverapprox(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fis_5fmultiset_5fsubset_5fstrict(s, v17, v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match requires_0_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s, v22, v23, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v14 { return Ok(None); }
let v15 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v15, v9]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s, v16, v12, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-ctn-multiset-subset"
pub fn eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s, a0);
s.leave();
result
}
pub(super) fn case_120_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fctn_5fmultiset_5fsubset, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2dctn_2dmultiset_2dsubset(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v109: Term, v104: Term, v99: Term) -> CheckResult<Term> {
let v110 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v109, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v104, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v99, v112) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v113)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v97: Term, v9: Term, v86: Term, v19: Term, v33: Term) -> CheckResult<Term> {
let v98 = match s.apply(v97, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v86, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v100, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v105, v108) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v109, v104, v99)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v84: Term, v85: Term, v19: Term, v26: Term, v33: Term, v30: Term, v9: Term) -> CheckResult<Term> {
if v84 != v85 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v84) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v86 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v91, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v89, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v87, v96) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v97, v9, v86, v19, v33)
}
pub(super) fn requires_3_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v74: Term, v75: Term, v9: Term, v26: Term, v19: Term, v33: Term, v30: Term) -> CheckResult<Term> {
if v74 != v75 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v74) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v76 = match eo__24str_5fvalue_5flen(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v77, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match eo__24str_5fflatten(s, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v80, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match eo__24str_5fflatten(s, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match eo__24str_5foverlap_5frec(s, v79, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_core(EvalOp::Gt, &[v76, v83]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match requires_2_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v84, v85, v19, v26, v33, v30, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v114)
}
pub(super) fn requires_4_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v64: Term, v65: Term, v26: Term, v9: Term, v19: Term, v33: Term, v30: Term) -> CheckResult<Term> {
if v64 != v65 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v64) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v66 = match eo__24str_5fvalue_5flen(s, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v67, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match eo__24str_5fflatten(s, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v70, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24str_5fflatten(s, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match eo__24str_5foverlap_5frec(s, v69, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_core(EvalOp::Gt, &[v66, v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match requires_3_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v74, v75, v9, v26, v19, v33, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v115)
}
pub(super) fn more_7_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v60: Term, v61: Term, v33: Term, v58: Term, v9: Term, v51: Term, v30: Term, v26: Term, v19: Term) -> CheckResult<Option<Term>> {
let v62 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v62 { return Ok(None); }
if v61 != v33 { return Ok(None); }
if v58 != v9 { return Ok(None); }
let v63 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v63 { return Ok(None); }
let v64 = match eo__24str_5fis_5fempty(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match requires_4_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v64, v65, v26, v9, v19, v33, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v116))
}
pub(super) fn more_6_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v40: Term, v19: Term, v9: Term, v37: Term, v33: Term, v30: Term, v26: Term) -> CheckResult<Option<Term>> {
let v42 = match s.unapply(v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
if v47 != v19 { return Ok(None); }
if v44 != v9 { return Ok(None); }
let v49 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
let v56 = match s.unapply(v54) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v57, v58)) = v56 else { return Ok(None); }
;
let v59 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
more_7_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v60, v61, v33, v58, v9, v51, v30, v26, v19)
}
pub(super) fn more_5_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, v16: Term, v2: Term, v19: Term, v9: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v34 { return Ok(None); }
let v35 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
more_6_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v40, v19, v9, v37, v33, v30, v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_5_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v16, v2, v19, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-overlap-split-ctn"
pub fn eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, a0);
s.leave();
result
}
pub(super) fn case_121_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5foverlap_5fsplit_5fctn, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2doverlap_2dsplit_2dctn(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v139: Term, v26: Term, v40: Term, v47: Term, v54: Term, v30: Term, v138: Term) -> CheckResult<Term> {
let v140 = match s.apply(v139, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v141, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v145, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v146, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v144, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v142, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v140, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v138, v150) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v151)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v40: Term, v47: Term, v54: Term, v30: Term, v127: Term, v116: Term, v26: Term) -> CheckResult<Term> {
let v128 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.apply(v130, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v132, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v133, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v131, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v129, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v127, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v116, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v139, v26, v40, v47, v54, v30, v138)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v114: Term, v115: Term, v19: Term, v26: Term, v33: Term, v30: Term, v40: Term, v47: Term, v54: Term) -> CheckResult<Term> {
if v114 != v115 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v114) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v116 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v118, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v121, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v119, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v117, v126) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v40, v47, v54, v30, v127, v116, v26)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v102: Term, v113: Term, v19: Term, v26: Term, v33: Term, v30: Term, v40: Term, v47: Term, v54: Term) -> CheckResult<Term> {
let v114 = match s.builtin_core(EvalOp::Gt, &[v102, v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match requires_2_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v114, v115, v19, v26, v33, v30, v40, v47, v54) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v152)
}
pub(super) fn requires_4_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v100: Term, v101: Term, v33: Term, v54: Term, v19: Term, v26: Term, v30: Term, v40: Term, v47: Term) -> CheckResult<Term> {
if v100 != v101 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v100) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v102 = match eo__24str_5fvalue_5flen(s, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v104, v33]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24str_5fflatten(s, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.builtin_list(EvalOp::ListRev, &[v103, v106]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v109, v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match eo__24str_5fflatten(s, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.builtin_list(EvalOp::ListRev, &[v108, v111]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match eo__24str_5foverlap_5frec(s, v107, v112) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v102, v113, v19, v26, v33, v30, v40, v47, v54)
}
pub(super) fn requires_5_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v90: Term, v91: Term, v19: Term, v40: Term, v33: Term, v54: Term, v26: Term, v30: Term, v47: Term) -> CheckResult<Term> {
if v90 != v91 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v90) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v92 = match eo__24str_5fvalue_5flen(s, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v93, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match eo__24str_5fflatten(s, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v96, v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match eo__24str_5fflatten(s, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match eo__24str_5foverlap_5frec(s, v95, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.builtin_core(EvalOp::Gt, &[v92, v99]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match requires_4_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v100, v101, v33, v54, v19, v26, v30, v40, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v153)
}
pub(super) fn requires_6_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v87: Term, v88: Term, v54: Term, v19: Term, v40: Term, v33: Term, v26: Term, v30: Term, v47: Term) -> CheckResult<Term> {
if v87 != v88 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v87) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v89 = match eo__24str_5fvalue_5flen(s, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_core(EvalOp::IsZ, &[v89]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match requires_5_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v90, v91, v19, v40, v33, v54, v26, v30, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v154)
}
pub(super) fn requires_7_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v84: Term, v85: Term, v40: Term, v54: Term, v19: Term, v33: Term, v26: Term, v30: Term, v47: Term) -> CheckResult<Term> {
if v84 != v85 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v84) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v86 = match eo__24str_5fvalue_5flen(s, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.builtin_core(EvalOp::IsZ, &[v86]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match requires_6_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v87, v88, v54, v19, v40, v33, v26, v30, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v155)
}
pub(super) fn more_11_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v72: Term, v54: Term, v30: Term, v40: Term, v19: Term, v33: Term, v26: Term, v47: Term) -> CheckResult<Option<Term>> {
let v77 = match s.unapply(v72) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v78, v79)) = v77 else { return Ok(None); }
;
let v80 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v81 != v83 { return Ok(None); }
if v82 != v54 { return Ok(None); }
if v79 != v30 { return Ok(None); }
let v84 = match eo__24str_5fis_5fempty(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match requires_7_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v84, v85, v40, v54, v19, v33, v26, v30, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v156))
}
pub(super) fn more_10_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v60: Term, v62: Term, v61: Term, v26: Term, v58: Term, v40: Term, v47: Term, v54: Term, v30: Term, v19: Term, v33: Term) -> CheckResult<Option<Term>> {
if v60 != v62 { return Ok(None); }
if v61 != v26 { return Ok(None); }
let v63 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v64, v65)) = v63 else { return Ok(None); }
;
let v66 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v67, v68)) = v66 else { return Ok(None); }
;
let v69 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v67 != v69 { return Ok(None); }
if v68 != v40 { return Ok(None); }
let v70 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v71, v72)) = v70 else { return Ok(None); }
;
let v73 = match s.unapply(v71) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v74 != v76 { return Ok(None); }
if v75 != v47 { return Ok(None); }
more_11_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v72, v54, v30, v40, v19, v33, v26, v47)
}
pub(super) fn more_9_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v37: Term, v30: Term, v2: Term, v26: Term, v40: Term, v19: Term, v33: Term) -> CheckResult<Option<Term>> {
let v42 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
let v49 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
if v51 != v30 { return Ok(None); }
let v56 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v57, v58)) = v56 else { return Ok(None); }
;
let v59 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
let v62 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v60, v62, v61, v26, v58, v40, v47, v54, v30, v19, v33)
}
pub(super) fn more_8_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, v16: Term, v9: Term, v2: Term, v19: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v34 { return Ok(None); }
let v35 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v39 != v41 { return Ok(None); }
more_9_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v37, v30, v2, v26, v40, v19, v33)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_8_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v16, v9, v2, v19)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-overlap-endpoints-ctn"
pub fn eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, a0);
s.leave();
result
}
pub(super) fn case_122_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5foverlap_5fendpoints_5fctn, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dctn(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v113: Term, v43: Term, v26: Term, v112: Term, v110: Term, v108: Term) -> CheckResult<Term> {
let v114 = match s.apply(v113, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v114, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v112, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v110, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v117, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v108, v119) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v120)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v101: Term, v43: Term, v26: Term, v100: Term, v98: Term, v90: Term, v22: Term, v36: Term) -> CheckResult<Term> {
let v102 = match s.apply(v101, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v100, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v98, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v105, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v90, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v113, v43, v26, v112, v110, v108)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v88: Term, v89: Term, v22: Term, v29: Term, v26: Term, v36: Term, v43: Term) -> CheckResult<Term> {
if v88 != v89 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v88) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v90 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v93, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v91, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v99, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v101, v43, v26, v100, v98, v90, v22, v36)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v76: Term, v87: Term, v22: Term, v29: Term, v26: Term, v36: Term, v43: Term) -> CheckResult<Term> {
let v88 = match s.builtin_core(EvalOp::Gt, &[v76, v87]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match requires_2_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v88, v89, v22, v29, v26, v36, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v121)
}
pub(super) fn requires_4_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v74: Term, v75: Term, v29: Term, v43: Term, v22: Term, v26: Term, v36: Term) -> CheckResult<Term> {
if v74 != v75 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v74) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v76 = match eo__24str_5fvalue_5flen(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v78, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match eo__24str_5fflatten(s, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_list(EvalOp::ListRev, &[v77, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v83, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match eo__24str_5fflatten(s, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.builtin_list(EvalOp::ListRev, &[v82, v85]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24str_5foverlap_5frec(s, v81, v86) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v76, v87, v22, v29, v26, v36, v43)
}
pub(super) fn requires_5_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v71: Term, v72: Term, v43: Term, v29: Term, v22: Term, v26: Term, v36: Term) -> CheckResult<Term> {
if v71 != v72 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v71) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v73 = match eo__24str_5fvalue_5flen(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_core(EvalOp::IsZ, &[v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match requires_4_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v74, v75, v29, v43, v22, v26, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v122)
}
pub(super) fn more_9_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v71: Term, v43: Term, v29: Term, v22: Term, v26: Term, v36: Term) -> CheckResult<Option<Term>> {
let v72 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match requires_5_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v71, v72, v43, v29, v22, v26, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v123))
}
pub(super) fn more_8_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v60: Term, v61: Term, v36: Term, v58: Term, v43: Term, v26: Term, v48: Term, v29: Term, v22: Term) -> CheckResult<Option<Term>> {
let v62 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v62 { return Ok(None); }
if v61 != v36 { return Ok(None); }
let v63 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v64, v65)) = v63 else { return Ok(None); }
;
let v66 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v67, v68)) = v66 else { return Ok(None); }
;
let v69 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v67 != v69 { return Ok(None); }
if v68 != v43 { return Ok(None); }
if v65 != v26 { return Ok(None); }
let v70 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v48 != v70 { return Ok(None); }
let v71 = match eo__24str_5fis_5fempty(s, v26) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v71, v43, v29, v22, v26, v36)
}
pub(super) fn more_7_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v42: Term, v44: Term, v40: Term, v26: Term, v9: Term, v2: Term, v22: Term, v36: Term, v43: Term, v29: Term) -> CheckResult<Option<Term>> {
if v42 != v44 { return Ok(None); }
if v40 != v26 { return Ok(None); }
let v45 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v45 { return Ok(None); }
let v46 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
if v54 != v22 { return Ok(None); }
let v56 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v57, v58)) = v56 else { return Ok(None); }
;
let v59 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
more_8_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v60, v61, v36, v58, v43, v26, v48, v29, v22)
}
pub(super) fn more_6_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, v21: Term, v23: Term, v19: Term, v12: Term, v9: Term, v2: Term, v22: Term) -> CheckResult<Option<Term>> {
if v21 != v23 { return Ok(None); }
let v24 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v30 { return Ok(None); }
let v31 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
let v38 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v42, v44, v40, v26, v9, v2, v22, v36, v43, v29)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v21, v23, v19, v12, v9, v2, v22)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-overlap-endpoints-indexof"
pub fn eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, a0);
s.leave();
result
}
pub(super) fn case_123_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5foverlap_5fendpoints_5findexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dindexof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_30_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_120_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_121_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_122_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_123_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v175: Term, v178: Term, v173: Term, v171: Term, v9: Term, v169: Term, v36: Term, v33: Term, v168: Term, v166: Term) -> CheckResult<Term> {
let v179 = match s.apply(v175, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v173, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v171, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v181, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v169, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.apply(v184, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v185, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v183, v186) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v168, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v166, v188) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v189)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v22: Term, v29: Term, v43: Term, v50: Term, v57: Term, v33: Term, v9: Term, v36: Term, v166: Term) -> CheckResult<Term> {
let v167 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.apply(v167, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v170, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.apply(v172, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v174, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.apply(v176, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v177, v33) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v175, v178, v173, v171, v9, v169, v36, v33, v168, v166)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v43: Term, v50: Term, v57: Term, v33: Term, v154: Term, v9: Term, v143: Term, v22: Term, v29: Term, v36: Term) -> CheckResult<Term> {
let v155 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v157, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v159, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.apply(v160, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v158, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v156, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v154, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v164, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v143, v165) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v22, v29, v43, v50, v57, v33, v9, v36, v166)
}
pub(super) fn requires_3_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v141: Term, v142: Term, v22: Term, v29: Term, v36: Term, v33: Term, v43: Term, v50: Term, v57: Term, v9: Term) -> CheckResult<Term> {
if v141 != v142 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v141) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v143 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v145, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v147, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v150, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.apply(v148, v151) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v146, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v144, v153) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v43, v50, v57, v33, v154, v9, v143, v22, v29, v36)
}
pub(super) fn more_4_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v129: Term, v140: Term, v22: Term, v29: Term, v36: Term, v33: Term, v43: Term, v50: Term, v57: Term, v9: Term) -> CheckResult<Term> {
let v141 = match s.builtin_core(EvalOp::Gt, &[v129, v140]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match requires_3_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v141, v142, v22, v29, v36, v33, v43, v50, v57, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v190)
}
pub(super) fn requires_5_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v127: Term, v128: Term, v36: Term, v57: Term, v22: Term, v29: Term, v33: Term, v43: Term, v50: Term, v9: Term) -> CheckResult<Term> {
if v127 != v128 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v127) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v129 = match eo__24str_5fvalue_5flen(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v131, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match eo__24str_5fflatten(s, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.builtin_list(EvalOp::ListRev, &[v130, v133]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v136, v57]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match eo__24str_5fflatten(s, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.builtin_list(EvalOp::ListRev, &[v135, v138]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match eo__24str_5foverlap_5frec(s, v134, v139) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v129, v140, v22, v29, v36, v33, v43, v50, v57, v9)
}
pub(super) fn requires_6_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v117: Term, v118: Term, v22: Term, v43: Term, v36: Term, v57: Term, v29: Term, v33: Term, v50: Term, v9: Term) -> CheckResult<Term> {
if v117 != v118 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v117) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v119 = match eo__24str_5fvalue_5flen(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v120, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match eo__24str_5fflatten(s, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v123, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match eo__24str_5fflatten(s, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24str_5foverlap_5frec(s, v122, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.builtin_core(EvalOp::Gt, &[v119, v126]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match requires_5_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v127, v128, v36, v57, v22, v29, v33, v43, v50, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v191)
}
pub(super) fn requires_7_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v114: Term, v115: Term, v57: Term, v22: Term, v43: Term, v36: Term, v29: Term, v33: Term, v50: Term, v9: Term) -> CheckResult<Term> {
if v114 != v115 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v114) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v116 = match eo__24str_5fvalue_5flen(s, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.builtin_core(EvalOp::IsZ, &[v116]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match requires_6_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v117, v118, v22, v43, v36, v57, v29, v33, v50, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v192)
}
pub(super) fn requires_8_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v111: Term, v112: Term, v43: Term, v57: Term, v22: Term, v36: Term, v29: Term, v33: Term, v50: Term, v9: Term) -> CheckResult<Term> {
if v111 != v112 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v111) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v113 = match eo__24str_5fvalue_5flen(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.builtin_core(EvalOp::IsZ, &[v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match requires_7_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v114, v115, v57, v22, v43, v36, v29, v33, v50, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v193)
}
pub(super) fn more_14_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v33: Term, v43: Term, v57: Term, v22: Term, v36: Term, v29: Term, v50: Term, v9: Term) -> CheckResult<Option<Term>> {
let v111 = match eo__24str_5fis_5fempty(s, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match requires_8_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v111, v112, v43, v57, v22, v36, v29, v33, v50, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v194))
}
pub(super) fn more_13_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v98: Term, v57: Term, v99: Term, v33: Term, v75: Term, v9: Term, v68: Term, v36: Term, v43: Term, v22: Term, v29: Term, v50: Term) -> CheckResult<Option<Term>> {
let v100 = match s.unapply(v98) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v101, v102)) = v100 else { return Ok(None); }
;
let v103 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v101 != v103 { return Ok(None); }
if v102 != v57 { return Ok(None); }
if v99 != v33 { return Ok(None); }
if v75 != v9 { return Ok(None); }
let v104 = match s.unapply(v68) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v105, v106)) = v104 else { return Ok(None); }
;
let v107 = match s.unapply(v105) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v108, v109)) = v107 else { return Ok(None); }
;
let v110 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v108 != v110 { return Ok(None); }
if v109 != v36 { return Ok(None); }
if v106 != v33 { return Ok(None); }
more_14_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v33, v43, v57, v22, v36, v29, v50, v9)
}
pub(super) fn more_12_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v81: Term, v29: Term, v78: Term, v43: Term, v50: Term, v57: Term, v33: Term, v75: Term, v9: Term, v68: Term, v36: Term, v22: Term) -> CheckResult<Option<Term>> {
if v81 != v29 { return Ok(None); }
let v83 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.unapply(v84) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v87, v88)) = v86 else { return Ok(None); }
;
let v89 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v87 != v89 { return Ok(None); }
if v88 != v43 { return Ok(None); }
let v90 = match s.unapply(v85) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v94, v95)) = v93 else { return Ok(None); }
;
let v96 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v96 { return Ok(None); }
if v95 != v50 { return Ok(None); }
let v97 = match s.unapply(v92) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v98, v99)) = v97 else { return Ok(None); }
;
more_13_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v98, v57, v99, v33, v75, v9, v68, v36, v43, v22, v29, v50)
}
pub(super) fn more_11_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v63: Term, v64: Term, v22: Term, v61: Term, v29: Term, v43: Term, v50: Term, v57: Term, v33: Term, v9: Term, v36: Term) -> CheckResult<Option<Term>> {
let v65 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v63 != v65 { return Ok(None); }
if v64 != v22 { return Ok(None); }
let v66 = match s.unapply(v61) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v67, v68)) = v66 else { return Ok(None); }
;
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v70 != v72 { return Ok(None); }
let v73 = match s.unapply(v71) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v80, v81)) = v79 else { return Ok(None); }
;
let v82 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v80 != v82 { return Ok(None); }
more_12_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v81, v29, v78, v43, v50, v57, v33, v75, v9, v68, v36, v22)
}
pub(super) fn more_10_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v42: Term, v44: Term, v40: Term, v33: Term, v2: Term, v22: Term, v29: Term, v43: Term, v9: Term, v36: Term) -> CheckResult<Option<Term>> {
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
let v52 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v56 != v58 { return Ok(None); }
if v54 != v33 { return Ok(None); }
let v59 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
let v62 = match s.unapply(v60) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
more_11_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v63, v64, v22, v61, v29, v43, v50, v57, v33, v9, v36)
}
pub(super) fn more_9_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, v21: Term, v23: Term, v19: Term, v12: Term, v2: Term, v22: Term, v9: Term) -> CheckResult<Option<Term>> {
if v21 != v23 { return Ok(None); }
let v24 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v30 { return Ok(None); }
let v31 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v35 != v37 { return Ok(None); }
let v38 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v42, v44, v40, v33, v2, v22, v29, v43, v9, v36)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v21, v23, v19, v12, v2, v22, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-overlap-endpoints-replace"
pub fn eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, a0);
s.leave();
result
}
pub(super) fn case_124_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5foverlap_5fendpoints_5freplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2doverlap_2dendpoints_2dreplace(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_1_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s: &mut Store, v1: Term, v2: Term, a2: Term) -> CheckResult<Term> {
if v1 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a2)
}
pub(super) fn case_1_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24re_5fnullable(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match requires_1_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, v1, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
// EO program "$str_first_match_rec_smallest"
pub fn eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1058), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1058), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24re_5fnullable(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_0_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, v7, a2, v5, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn if_0_eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s: &mut Store, condition: Term, a2: Term, v5: Term, a1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v8 = match eo__24derivative(s, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, v2, v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5ffirst_5fmatch_5frec(s: &mut Store, condition: Term, a3: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, v5, a1, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Add, &[a3, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v4, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5ffirst_5fmatch_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24str_5feval_5fstr_5fin_5fre_5frec(s, v1, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_1_eo__24str_5ffirst_5fmatch_5frec(s, v2, a3, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
// EO program "$str_first_match_rec"
pub fn eo__24str_5ffirst_5fmatch_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(1057), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5ffirst_5fmatch_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1057), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5ffirst_5fmatch_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5ffirst_5fmatch_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5ffirst_5fmatch_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5ffirst_5fmatch_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24str_5feval_5fstr_5fin_5fre_5frec(s, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match if_0_eo__24str_5ffirst_5fmatch_5frec(s, v10, a3, v5, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn if_0_eo__24str_5ffirst_5fmatch_5frec(s: &mut Store, condition: Term, a3: Term, v5: Term, v2: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, v15, a1, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Add, &[a3, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Add, &[a3, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5ffirst_5fmatch_5frec(s, v2, a1, a2, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, v36: Term, v37: Term, v35: Term, v32: Term, v30: Term, v12: Term) -> CheckResult<Term> {
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v32, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24str_5ffirst_5fmatch_5frec(s, v30, v12, v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, v24: Term, v25: Term, v15: Term, v9: Term, v12: Term) -> CheckResult<Term> {
if v24 != v25 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v24) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Length, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Extract, &[v15, v9, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v26, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24str_5fflatten(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v36, v37, v35, v32, v30, v12)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, v62: Term, v63: Term, v61: Term, v58: Term, v56: Term, v12: Term) -> CheckResult<Term> {
let v64 = match s.apply(v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v61, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v58, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24str_5ffirst_5fmatch_5frec(s, v56, v12, v66, v67) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v68)
}
pub(super) fn requires_3_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, v50: Term, v51: Term, v15: Term, v9: Term, v12: Term) -> CheckResult<Term> {
if v50 != v51 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v50) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v52 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_core(EvalOp::Length, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.builtin_core(EvalOp::Extract, &[v15, v9, v53]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v52, v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match eo__24str_5fflatten(s, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v59, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v62, v63, v61, v58, v56, v12)
}
pub(super) fn if_4_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, condition: Term, v15: Term, v9: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v47 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v47)
}
Some(false) => {
let v48 = match s.builtin_core(EvalOp::Length, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::Extract, &[v15, v9, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::IsStr, &[v49]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match requires_3_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v50, v51, v15, v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match eo__24pair_5ffirst(s, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.builtin_core(EvalOp::Add, &[v9, v70]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v71)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, condition: Term, v15: Term, v9: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v21 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
Some(false) => {
let v22 = match s.builtin_core(EvalOp::Length, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Extract, &[v15, v9, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::IsStr, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match requires_1_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v24, v25, v15, v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match eo__24pair_5ffirst(s, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.builtin_core(EvalOp::Eq, &[v44, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match if_4_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v46, v15, v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v72)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_6_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, v73: Term, v2: Term, v15: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v73 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v73) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v74 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v80)
}
pub(super) fn more_7_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, v18: Term, v19: Term, v15: Term, v9: Term, v12: Term, v2: Term) -> CheckResult<Option<Term>> {
let v20 = match s.builtin_core(EvalOp::Or, &[v18, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match if_5_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v20, v15, v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match requires_6_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v73, v2, v15, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v81))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.builtin_core(EvalOp::Length, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Gt, &[v9, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v18, v19, v15, v9, v12, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-indexof-re-eval"
pub fn eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, a0);
s.leave();
result
}
pub(super) fn case_125_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5findexof_5fre_5feval, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2dindexof_2dre_2deval(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s: &mut Store, v23: Term, v30: Term, v21: Term, v12: Term) -> CheckResult<Term> {
let v31 = match s.apply(v23, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24str_5ffirst_5fmatch_5frec(s, v21, v12, v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s: &mut Store, v17: Term, v18: Term, v15: Term, v12: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v19, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24str_5fflatten(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s, v23, v30, v21, v12)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s: &mut Store, v35: Term, v2: Term, v15: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v35 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v35) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v36 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v36, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
pub(super) fn case_0_eo__24str_5feval_5freplace_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v8 { return Ok(None); }
Ok(Some(a0))
}
pub(super) fn more_0_eo__24str_5feval_5freplace_5fre(s: &mut Store, a0: Term, v2: Term, v14: Term, v12: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Length, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Extract, &[a0, v2, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v15, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v12, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_1_eo__24str_5feval_5freplace_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40pair, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[v5, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Extract, &[a0, v8, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5feval_5freplace_5fre(s, a0, v2, v14, v12)
}
pub(super) fn body_eo__24str_5feval_5freplace_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5feval_5freplace_5fre(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5feval_5freplace_5fre(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_eval_replace_re"
pub fn eo__24str_5feval_5freplace_5fre(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5feval_5freplace_5fre(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s: &mut Store, v15: Term, v12: Term, v9: Term, v34: Term, v2: Term) -> CheckResult<Option<Term>> {
let v35 = match eo__24str_5feval_5freplace_5fre(s, v15, v12, v9, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match requires_2_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s, v35, v2, v15, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v43))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_str_2ereplace_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.builtin_core(EvalOp::IsStr, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match requires_1_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s, v17, v18, v15, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s, v15, v12, v9, v34, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-replace-re-eval"
pub fn eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s, a0);
s.leave();
result
}
pub(super) fn case_126_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5freplace_5fre_5feval, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2dreplace_2dre_2deval(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s: &mut Store, v38: Term, v2: Term, v15: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v38 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v38) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v39 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v39, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
pub(super) fn if_0_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::Eq, &[a1, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn if_1_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v22 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, v24, a2, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
Some(false) => {
let v27 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match eo__24str_5ffirst_5fmatch_5frec_5fsmallest(s, v55, a2, v56) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
Some(false) => {
let v58 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v58)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_4_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, v35: Term, v63: Term) -> CheckResult<Term> {
let v64 = match s.apply(v35, v63) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v64)
}
pub(super) fn case_2_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Add, &[a4, v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, a1, a2, a3, v8])))
}
// EO program "$str_eval_replace_re_all_rec"
pub fn eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(1055), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1055), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, a0, a1, a2, a3, a4) {
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
pub(super) fn step_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Next<[Term; 5]>> {
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
if let Some(found) = match case_0_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if a4 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v13, v12, v10, v5, v2, a2, a1, a3)
}
pub(super) fn more_3_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, v44: Term, v45: Term, v43: Term, v41: Term, v5: Term, v2: Term, a2: Term, v38: Term, a3: Term, v37: Term, v35: Term) -> CheckResult<Term> {
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v46, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v43, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24str_5feval_5fstr_5fin_5fre_5frec(s, v41, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match if_2_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v52, v5, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.builtin_core(EvalOp::Add, &[v59, v60]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v2, v38, a2, a3, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v37, v62) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v35, v63)
}
pub(super) fn if_5_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, condition: Term, a1: Term, v5: Term, v2: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v31 = match s.builtin_core(EvalOp::Concat, &[a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v2, v31, a2, a3, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v44, v45, v43, v41, v5, v2, a2, v38, a3, v37, v35)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_6_eo__24str_5feval_5freplace_5fre_5fall_5frec(s: &mut Store, v13: Term, v12: Term, v10: Term, v5: Term, v2: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v14 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v12, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24str_5feval_5fstr_5fin_5fre_5frec(s, v10, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_1_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v21, v5, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::Eq, &[v28, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match if_5_eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v30, a1, v5, v2, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v65)))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s: &mut Store, v27: Term, v30: Term, v26: Term, v25: Term, v22: Term, v23: Term, v9: Term, v19: Term, v2: Term, v15: Term, v12: Term) -> CheckResult<Term> {
let v31 = match s.apply(v27, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v26, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v25, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24str_5feval_5freplace_5fre_5fall_5frec(s, v22, v23, v35, v9, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListSingletonElim, &[v19, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match requires_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s, v38, v2, v15, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v46)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s: &mut Store, v17: Term, v18: Term, v15: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v20, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fflatten(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s, v27, v30, v26, v25, v22, v23, v9, v19, v2, v15, v12)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.builtin_core(EvalOp::IsStr, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match requires_2_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s, v17, v18, v15, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-replace-re-all-eval"
pub fn eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s, a0);
s.leave();
result
}
pub(super) fn case_127_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5freplace_5fre_5fall_5feval, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2dreplace_2dre_2dall_2deval(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_31_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_124_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_125_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_126_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_127_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_7_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_28_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_29_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_30_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_31_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_1_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_4_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_5_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_6_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_7_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fseq_2deval_2dop(s: &mut Store, v7: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v7 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn case_0_eo__24seq_5felement_5fof_5funit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24seq_5felement_5fof_5funit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24seq_5felement_5fof_5funit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$seq_element_of_unit"
pub fn eo__24seq_5felement_5fof_5funit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24seq_5felement_5fof_5funit(s, a0);
s.leave();
result
}
pub(super) fn requires_0_eo__24seq_5feval(s: &mut Store, v7: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v7 != v8 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v9 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v10, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListNth, &[v9, v11, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24seq_5felement_5fof_5funit(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
pub(super) fn case_0_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_seq_2enth, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24is_5fseq_5fconst(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match requires_0_eo__24seq_5feval(s, v7, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_1_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v4, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24str_5fvalue_5flen(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24seq_5feval(s: &mut Store, v7: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.builtin_list(EvalOp::ListSingletonElim, &[v7, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24seq_5fsubsequence_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_seq_2eempty, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_1_eo__24seq_5fsubsequence_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match eo__24eo_5ftypeof(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_seq_2eempty, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn case_3_eo__24seq_5fsubsequence_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[a0, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[a1, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v12, v14, v2])))
}
// EO program "$seq_subsequence_rec"
pub fn eo__24seq_5fsubsequence_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(983), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24seq_5fsubsequence_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(983), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24seq_5fsubsequence_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24seq_5fsubsequence_5frec(s, a0, a1, a2) {
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
pub(super) fn step_eo__24seq_5fsubsequence_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24seq_5fsubsequence_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24seq_5fsubsequence_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24seq_5fsubsequence_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24seq_5fsubsequence_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_2_eo__24seq_5fsubsequence_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24seq_5fsubsequence_5frec(s, v12, v14, a1, v3)
}
pub(super) fn more_0_eo__24seq_5fsubsequence_5frec(s: &mut Store, v12: Term, v14: Term, a1: Term, v3: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Add, &[a1, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24seq_5fsubsequence_5frec(s, v16, v18, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v15, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v20)))
}
pub(super) fn if_2_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v13, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eo_5ftypeof(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_seq_2eempty, &[v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.builtin_core(EvalOp::Add, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v18, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24seq_5fsubsequence_5frec(s, v5, v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_3_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Add, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::IsNeg, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_2_eo__24seq_5feval(s, v12, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListSingletonElim, &[v10, v21]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24seq_5ffind(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
Ok(Some(a2))
}
pub(super) fn case_1_eo__24seq_5ffind(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn case_1_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
pub(super) fn if_0_eo__24seq_5fis_5fprefix(s: &mut Store, condition: Term, v9: Term, v20: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24are_5fdistinct_5fterms_5ftype(s, v9, v20, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24seq_5fis_5fprefix(s: &mut Store, v26: Term, v27: Term) -> CheckResult<Term> {
if v26 != v27 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v26) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v28 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
pub(super) fn more_2_eo__24seq_5fis_5fprefix(s: &mut Store, v19: Term, v9: Term, v20: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v21 = match s.construct(Constructor::eo_seq_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.builtin_core(EvalOp::Eq, &[v9, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_0_eo__24seq_5fis_5fprefix(s, v22, v9, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match requires_1_eo__24seq_5fis_5fprefix(s, v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v29)))
}
pub(super) fn case_2_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
let v11 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
more_2_eo__24seq_5fis_5fprefix(s, v19, v9, v20)
}
pub(super) fn case_3_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
pub(super) fn cases_0_0_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if let Some(found) = match case_0_eo__24seq_5fis_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24seq_5fis_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24seq_5fis_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24seq_5fis_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
let v11 = match s.destruct(Constructor::eo_seq_2eempty, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v11 else { return Ok(None); }
;
let v12 = fields[0];
let v13 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v17)))
}
pub(super) fn cases_0_1_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
if let Some(found) = match case_4_eo__24seq_5fis_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn step_eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match cases_0_0_eo__24seq_5fis_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24seq_5fis_5fprefix(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24seq_5fis_5fprefix(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24seq_5fis_5fprefix(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$seq_is_prefix"
pub fn eo__24seq_5fis_5fprefix(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(982), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24seq_5fis_5fprefix(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(982), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
// EO program "$seq_find"
pub fn eo__24seq_5ffind(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(980), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24seq_5ffind(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(980), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24seq_5ffind(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24seq_5ffind(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24seq_5ffind(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24seq_5ffind(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24seq_5ffind(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24seq_5fis_5fprefix(s, a1, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_0_eo__24seq_5ffind(s, v10, a2, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn if_0_eo__24seq_5ffind(s: &mut Store, condition: Term, a2: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[a2, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24seq_5ffind(s, v2, a1, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_3_eo__24seq_5feval(s: &mut Store, v9: Term, v10: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v9 != v10 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v11, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v13, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24seq_5ffind(s, v12, v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::IsNeg, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Not, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
pub(super) fn requires_4_eo__24seq_5feval(s: &mut Store, v7: Term, v8: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v7 != v8 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v9 = match eo__24is_5fseq_5fconst(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match requires_3_eo__24seq_5feval(s, v9, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
pub(super) fn case_4_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24is_5fseq_5fconst(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match requires_4_eo__24seq_5feval(s, v7, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn if_5_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v30, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24eo_5ftypeof(s, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_seq_2eempty, &[v32]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v35, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v37, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24seq_5ffind(s, v36, v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v41, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24seq_5fsubsequence_5frec(s, v34, v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v50 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v50, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24eo_5ftypeof(s, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_seq_2eempty, &[v52]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v53)
}
Some(false) => {
let v54 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v54, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v56, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24seq_5ffind(s, v55, v57, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match eo__24str_5fvalue_5flen(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.builtin_core(EvalOp::Add, &[v59, v60]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match eo__24str_5fvalue_5flen(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v63, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24seq_5fsubsequence_5frec(s, v61, v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v65)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_7_eo__24seq_5feval(s: &mut Store, v46: Term, v2: Term, v8: Term, v5: Term, v45: Term, v22: Term, v44: Term, v21: Term) -> CheckResult<Term> {
let v47 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v46, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match eo__24str_5fvalue_5flen(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::IsNeg, &[v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match if_6_eo__24seq_5feval(s, v49, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.builtin_list(EvalOp::ListConcat, &[v45, v47, v66]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_list(EvalOp::ListConcat, &[v22, v44, v67]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.builtin_list(EvalOp::ListSingletonElim, &[v21, v68]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v69)
}
pub(super) fn if_8_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v8)
}
Some(false) => {
let v21 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v23, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v25, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24seq_5ffind(s, v24, v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::IsNeg, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_5_eo__24seq_5feval(s, v29, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24seq_5feval(s, v46, v2, v8, v5, v45, v22, v44, v21)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_9_eo__24seq_5feval(s: &mut Store, v12: Term, v13: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v12 != v13 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v12) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v14 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v14, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v16, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24seq_5ffind(s, v15, v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::IsNeg, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match if_8_eo__24seq_5feval(s, v20, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
pub(super) fn requires_10_eo__24seq_5feval(s: &mut Store, v10: Term, v11: Term, v5: Term, v8: Term, v2: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match eo__24is_5fseq_5fconst(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match requires_9_eo__24seq_5feval(s, v12, v13, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v71)
}
pub(super) fn case_5_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24is_5fseq_5fconst(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match requires_10_eo__24seq_5feval(s, v10, v11, v5, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v72))
}
pub(super) fn case_0_eo__24seq_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.destruct(Constructor::eo_seq_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_seq_2eempty, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v8)))
}
pub(super) fn case_2_eo__24seq_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
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
// EO program "$seq_eval_replace_all_rec"
pub fn eo__24seq_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(979), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24seq_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(979), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24seq_5feval_5freplace_5fall_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term) -> CheckResult<Term> {
loop {
match step_eo__24seq_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) {
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
pub(super) fn step_eo__24seq_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Next<[Term; 5]>> {
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
if let Some(found) = match case_0_eo__24seq_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24seq_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24seq_5feval_5freplace_5fall_5frec(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24seq_5feval_5freplace_5fall_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
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
let v11 = match eo__24seq_5fis_5fprefix(s, a1, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_0_eo__24seq_5feval_5freplace_5fall_5frec(s, v11, a4, v2, a1, a2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v21)))
}
pub(super) fn if_0_eo__24seq_5feval_5freplace_5fall_5frec(s: &mut Store, condition: Term, a4: Term, v2: Term, a1: Term, a2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[a4, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24seq_5feval_5freplace_5fall_5frec(s, v2, a1, a2, v14, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListConcat, &[v12, a2, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24seq_5feval_5freplace_5fall_5frec(s, v2, a1, a2, v18, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::Cons, &[v17, v5, v19]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_11_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v8)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v16, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v18, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v20, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24str_5fvalue_5flen(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24seq_5feval_5freplace_5fall_5frec(s, v17, v19, v21, v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListSingletonElim, &[v15, v24]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_12_eo__24seq_5feval(s: &mut Store, v10: Term, v11: Term, v5: Term, v8: Term, v2: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match eo__24str_5fvalue_5flen(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[v12, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_11_eo__24seq_5feval(s, v14, v8, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn case_6_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24is_5fseq_5fconst(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_12_eo__24seq_5feval(s, v10, v11, v5, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn if_13_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v19, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5ftypeof(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_seq_2eempty, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
Some(false) => {
let v23 = match eo__24str_5fvalue_5flen(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v24, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24seq_5fsubsequence_5frec(s, v2, v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match eo__24str_5fvalue_5flen(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_13_eo__24seq_5feval(s, v18, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v28, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24seq_5ffind(s, v27, v29, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24seq_5feval(s: &mut Store, condition: Term, v8: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match eo__24str_5fvalue_5flen(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::Gt, &[v2, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match if_14_eo__24seq_5feval(s, v15, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_16_eo__24seq_5feval(s: &mut Store, v10: Term, v11: Term, v2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match s.builtin_core(EvalOp::IsNeg, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match if_15_eo__24seq_5feval(s, v12, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn case_7_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match eo__24is_5fseq_5fconst(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_16_eo__24seq_5feval(s, v10, v11, v2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn cases_0_1_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_8_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v7, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v9, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24seq_5fis_5fprefix(s, v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn requires_17_eo__24seq_5feval(s: &mut Store, v9: Term, v10: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v9 != v10 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v12, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListRev, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v16, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListRev, &[v15, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24seq_5fis_5fprefix(s, v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
pub(super) fn requires_18_eo__24seq_5feval(s: &mut Store, v7: Term, v8: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v7 != v8 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v9 = match eo__24is_5fseq_5fconst(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match requires_17_eo__24seq_5feval(s, v9, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_9_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2esuffixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24is_5fseq_5fconst(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_18_eo__24seq_5feval(s, v7, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn if_19_eo__24seq_5feval(s: &mut Store, condition: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v11, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_seq_2eempty, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Add, &[v2, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v17, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24seq_5fsubsequence_5frec(s, v2, v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_10_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2eat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[v2, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match if_19_eo__24seq_5feval(s, v10, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListSingletonElim, &[v7, v20]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn requires_20_eo__24seq_5feval(s: &mut Store, v4: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v4 != v5 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v8, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListRev, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_list(EvalOp::ListSingletonElim, &[v6, v10]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
pub(super) fn case_11_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24is_5fseq_5fconst(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match requires_20_eo__24seq_5feval(s, v4, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn cases_0_2_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_12_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
Ok(Some(a0))
}
pub(super) fn cases_0_3_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$seq_eval"
pub fn eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(978), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24seq_5feval(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(978), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_3_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v9, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24seq_5feval(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListConcat, &[v8, v10, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24seq_5feval(s, v7, v14)
}
pub(super) fn cases_0_0_eo__24seq_5feval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24seq_5feval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fseq_2deval_2dop(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24seq_5feval(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_0_eo__24eo_5fprog_5fseq_2deval_2dop(s, v7, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fseq_2deval_2dop(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fseq_2deval_2dop(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_seq-eval-op"
pub fn eo__24eo_5fprog_5fseq_2deval_2dop(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fseq_2deval_2dop(s, a0);
s.leave();
result
}
pub(super) fn case_128_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eseq_5feval_5fop, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fseq_2deval_2dop(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj(s: &mut Store, v17: Term, v11: Term, v15: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v17, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj(s, v17, v11, v15)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_5fsingleton_5finj(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_5fsingleton_5finj(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets_singleton_inj"
pub fn eo__24eo_5fprog_5fsets_5fsingleton_5finj(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_5fsingleton_5finj(s, a0);
s.leave();
result
}
pub(super) fn case_129_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fsingleton_5finj, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fsets_5fsingleton_5finj(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_1_eo__24eo_5fprog_5fsets_5fext(s: &mut Store, v13: Term, v28: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v13, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_5fext(s: &mut Store, v16: Term, v11: Term, v8: Term, v15: Term, v14: Term, v13: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v16, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v14, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__40sets_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v21, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fsets_5fext(s, v13, v28)
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_5fext(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__40sets_5fdeq_5fdiff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_5fext(s, v16, v11, v8, v15, v14, v13)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_5fext(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets_ext"
pub fn eo__24eo_5fprog_5fsets_5fext(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_5fext(s, a0);
s.leave();
result
}
pub(super) fn case_130_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fext, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fsets_5fext(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember(s: &mut Store, v2: Term, v12: Term, v11: Term, v10: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo_set_2echoose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v11, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v10, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2echoose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_set_2eempty, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember(s, v2, v12, v11, v10)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_5fchoose_5fmember(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_5fchoose_5fmember(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets_choose_member"
pub fn eo__24eo_5fprog_5fsets_5fchoose_5fmember(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_5fchoose_5fmember(s, a0);
s.leave();
result
}
pub(super) fn case_131_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fchoose_5fmember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fsets_5fchoose_5fmember(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_32_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_128_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_129_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_130_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_131_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fsets_2deval_2dop(s: &mut Store, v12: Term, v13: Term, v5: Term, v2: Term) -> CheckResult<Term> {
if v12 != v13 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v12) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
pub(super) fn case_1_eo__24set_5funion_5fto_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo_set_2eempty, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v3, v4)) = v2 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_2_eo__24set_5funion_5fto_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fnil(s, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
// EO program "$set_union_to_list"
pub fn eo__24set_5funion_5fto_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(985), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24set_5funion_5fto_5flist(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(985), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24set_5funion_5fto_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24set_5funion_5fto_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24set_5funion_5fto_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24set_5funion_5fto_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24set_5funion_5fto_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24set_5funion_5fto_5flist(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eval_5fsets_5fop(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24set_5funion_5fto_5flist(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24set_5funion_5fto_5flist(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListConcat, &[v7, v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_1_eo__24eval_5fsets_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$eval_sets_inter"
pub fn eo__24eval_5fsets_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(879), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eval_5fsets_5finter(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(879), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eval_5fsets_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eval_5fsets_5finter(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eval_5fsets_5finter(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eval_5fsets_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListFind, &[v7, a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsNeg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_1_eo__24eval_5fsets_5finter(s, v9, v5, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn requires_0_eo__24eval_5fsets_5finter(s: &mut Store, v11: Term, v12: Term, v2: Term, a1: Term) -> CheckResult<Term> {
if v11 != v12 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v11) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v13 = match eo__24eval_5fsets_5finter(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
pub(super) fn if_1_eo__24eval_5fsets_5finter(s: &mut Store, condition: Term, v5: Term, a1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24are_5fdistinct_5fterms_5flist_5frec(s, v5, a1, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match requires_0_eo__24eval_5fsets_5finter(s, v11, v12, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
Some(false) => {
let v15 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eval_5fsets_5finter(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24eval_5fsets_5fop(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24set_5funion_5fto_5flist(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24set_5funion_5fto_5flist(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eval_5fsets_5finter(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_1_eo__24eval_5fsets_5fminus(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$eval_sets_minus"
pub fn eo__24eval_5fsets_5fminus(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(880), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eval_5fsets_5fminus(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(880), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eval_5fsets_5fminus(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eval_5fsets_5fminus(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eval_5fsets_5fminus(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eval_5fsets_5fminus(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListFind, &[v7, a1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsNeg, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_1_eo__24eval_5fsets_5fminus(s, v9, v5, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn requires_0_eo__24eval_5fsets_5fminus(s: &mut Store, v11: Term, v12: Term, v5: Term, v2: Term, a1: Term) -> CheckResult<Term> {
if v11 != v12 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v11) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v13 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24eval_5fsets_5fminus(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
pub(super) fn if_1_eo__24eval_5fsets_5fminus(s: &mut Store, condition: Term, v5: Term, a1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24are_5fdistinct_5fterms_5flist_5frec(s, v5, a1, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match requires_0_eo__24eval_5fsets_5fminus(s, v11, v12, v5, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
Some(false) => {
let v18 = match eo__24eval_5fsets_5fminus(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24eval_5fsets_5fop(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_set_2eminus, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24set_5funion_5fto_5flist(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24set_5funion_5fto_5flist(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eval_5fsets_5fminus(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eval_5fsets_5fop(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eval_5fsets_5fop(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eval_5fsets_5fop(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eval_5fsets_5fop(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eval_sets_op"
pub fn eo__24eval_5fsets_5fop(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eval_5fsets_5fop(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2deval_2dop(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eval_5fsets_5fop(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListSetof, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24set_5funion_5fto_5flist(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListMeq, &[v7, v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match requires_0_eo__24eo_5fprog_5fsets_2deval_2dop(s, v12, v13, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2deval_2dop(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2deval_2dop(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-eval-op"
pub fn eo__24eo_5fprog_5fsets_2deval_2dop(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2deval_2dop(s, a0);
s.leave();
result
}
pub(super) fn case_132_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5feval_5fop, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fsets_2deval_2dop(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24bv_5fbitwidth(s, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Pow, &[v24, v26]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v20 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24bv_5fbitwidth(s, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsNeg, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s, v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
Some(false) => {
let v29 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24bv_5fbitwidth(s, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_3_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s: &mut Store, v11: Term, v37: Term) -> CheckResult<Option<Term>> {
let v38 = match s.apply(v11, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn more_2_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s: &mut Store, v2: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24bv_5fbitwidth(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::IsZ, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match if_1_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s, v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v16, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v12, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s, v11, v37)
}
pub(super) fn case_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s, v2, v12, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ubv_to_int_range"
pub fn eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s, a0);
s.leave();
result
}
pub(super) fn case_133_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eubv_5fto_5fint_5frange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fubv_5fto_5fint_5frange(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s: &mut Store, v14: Term, v15: Term, v9: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24bv_5fbitwidth(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListRepeat, &[v16, v17, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24iota_5frec(s, v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s: &mut Store, v26: Term, v2: Term, v9: Term) -> CheckResult<Term> {
if v26 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v26) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
pub(super) fn more_2_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s: &mut Store, v14: Term, v15: Term, v9: Term, v11: Term, v2: Term) -> CheckResult<Option<Term>> {
let v23 = match requires_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s, v14, v15, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24abconv_5fubv_5fto_5fint_5felim(s, v9, v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_list(EvalOp::ListSingletonElim, &[v11, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match requires_1_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s, v26, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn case_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_ubv_5fto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24bv_5fbitwidth(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::IsNeg, &[v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s, v14, v15, v9, v11, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_ubv-to-int-elim"
pub fn eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_134_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eubv_5fto_5fint_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fubv_2dto_2dint_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s: &mut Store, condition: Term, v11: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Pow, &[v19, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s: &mut Store, condition: Term, v11: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v17 = match s.builtin_core(EvalOp::IsNeg, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match if_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s, v17, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
Some(false) => {
let v22 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_2_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s: &mut Store, v26: Term, v2: Term, v11: Term, v9: Term) -> CheckResult<Term> {
if v26 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v26) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
pub(super) fn more_3_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s: &mut Store, v9: Term, v15: Term, v24: Term, v12: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v25 = match eo__24abconv_5fint_5fto_5fbv_5felim(s, v9, v15, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_list(EvalOp::ListSingletonElim, &[v12, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match requires_2_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s, v26, v2, v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn case_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.destruct(Constructor::eo_int_5fto_5fbv, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListRepeat, &[v13, v14, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::IsZ, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match if_1_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s, v16, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s, v9, v15, v24, v12, v2, v11)
}
pub(super) fn body_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_int-to-bv-elim"
pub fn eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_135_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eint_5fto_5fbv_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fint_2dto_2dbv_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_33_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_132_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_133_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_134_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_135_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5finstantiate(s: &mut Store, v9: Term, v10: Term, v4: Term, v7: Term, a0: Term) -> CheckResult<Term> {
if v9 != v10 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24substitute_5fsimul_5frec(s, v11, v4, v7, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
pub(super) fn case_0_eo__24is_5finstantiation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
// EO program "$is_instantiation"
pub fn eo__24is_5finstantiation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(906), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5finstantiation(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(906), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24is_5finstantiation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5finstantiation(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5finstantiation(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24is_5finstantiation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.destruct(Constructor::eo__24emb_5fVar, v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = fields[1];
let v10 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match eo__24eo_5ftypeof(s, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match requires_0_eo__24is_5finstantiation(s, v17, v9, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn requires_0_eo__24is_5finstantiation(s: &mut Store, v17: Term, v9: Term, v2: Term, v12: Term) -> CheckResult<Term> {
if v17 != v9 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v18 = match eo__24is_5finstantiation(s, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
pub(super) fn case_0_eo__24eo_5fprog_5finstantiate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match eo__24is_5finstantiation(s, v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match requires_0_eo__24eo_5fprog_5finstantiate(s, v9, v10, v4, v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn body_eo__24eo_5fprog_5finstantiate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5finstantiate(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_instantiate"
pub fn eo__24eo_5fprog_5finstantiate(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5finstantiate(s, a0, a1);
s.leave();
result
}
pub(super) fn case_136_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2einstantiate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v11 = match eo__24eo_5fprog_5finstantiate(s, v2, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_1_eo__24mk_5fskolems(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$mk_skolems"
pub fn eo__24mk_5fskolems(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(949), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fskolems(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(949), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fskolems(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fskolems(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fskolems(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5fskolems(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__40quantifiers_5fskolemize, &[a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Add, &[a2, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24mk_5fskolems(s, v2, a1, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fskolemize(s: &mut Store, v20: Term, v11: Term, v8: Term) -> CheckResult<Term> {
if v20 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v20) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24mk_5fskolems(s, v11, v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24substitute_5fsimul_5frec(s, v21, v23, v11, v28, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fskolemize(s: &mut Store, v17: Term, v18: Term, v11: Term, v8: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListSetof, &[v19, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match requires_0_eo__24eo_5fprog_5fskolemize(s, v20, v11, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
pub(super) fn more_2_eo__24eo_5fprog_5fskolemize(s: &mut Store, v15: Term, v16: Term, v11: Term, v8: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24is_5fclosed_5frec(s, v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match requires_1_eo__24eo_5fprog_5fskolemize(s, v17, v18, v11, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn case_0_eo__24eo_5fprog_5fskolemize(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v12 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fskolemize(s, v15, v16, v11, v8)
}
pub(super) fn body_eo__24eo_5fprog_5fskolemize(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fprog_5fskolemize(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_skolemize"
pub fn eo__24eo_5fprog_5fskolemize(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fskolemize(s, a0);
s.leave();
result
}
pub(super) fn case_137_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eskolemize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v8 = match eo__24eo_5fprog_5fskolemize(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_0_eo__24eo_5fprog_5fskolem_5fintro(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fskolem_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fskolem_5fintro(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_skolem_intro"
pub fn eo__24eo_5fprog_5fskolem_5fintro(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fskolem_5fintro(s, a0);
s.leave();
result
}
pub(super) fn case_138_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eskolem_5fintro, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fskolem_5fintro(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5falpha_5fequiv(s: &mut Store, v18: Term, v19: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24substitute_5fsimul_5frec(s, v22, a0, a1, a2, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn requires_1_eo__24eo_5fprog_5falpha_5fequiv(s: &mut Store, v15: Term, v16: Term, a0: Term, a2: Term, a1: Term) -> CheckResult<Term> {
if v15 != v16 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v15) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a2, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match requires_0_eo__24eo_5fprog_5falpha_5fequiv(s, v18, v19, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn requires_2_eo__24eo_5fprog_5falpha_5fequiv(s: &mut Store, v12: Term, v13: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if v12 != v13 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v12) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a0, a1, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_1_eo__24eo_5fprog_5falpha_5fequiv(s, v15, v16, a0, a2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
pub(super) fn more_3_eo__24eo_5fprog_5falpha_5fequiv(s: &mut Store, v10: Term, v11: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v12 = match s.builtin_core(EvalOp::And, &[v10, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match requires_2_eo__24eo_5fprog_5falpha_5fequiv(s, v12, v13, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_0_eo__24is_5frenaming_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn case_1_eo__24is_5frenaming_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.destruct(Constructor::eo__24emb_5fVar, v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = fields[1];
let v10 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.destruct(Constructor::eo__24emb_5fVar, v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
if v19 != v9 { return Ok(None); }
Ok(Some(Next::Again([v2, v12])))
}
pub(super) fn step_eo__24is_5frenaming_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24is_5frenaming_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5frenaming_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24is_5frenaming_5frec(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24is_5frenaming_5frec(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$is_renaming_rec"
pub fn eo__24is_5frenaming_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(912), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5frenaming_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(912), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_1_eo__24is_5fvar_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$is_var_list"
pub fn eo__24is_5fvar_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(915), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fvar_5flist(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(915), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24is_5fvar_5flist(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24is_5fvar_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fvar_5flist(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24is_5fvar_5flist(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsVar, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24is_5fvar_5flist(s, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn if_0_eo__24is_5fvar_5flist(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match eo__24is_5fvar_5flist(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24eo_5fprog_5falpha_5fequiv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24is_5fvar_5flist(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_list(EvalOp::ListSetof, &[v1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.builtin_core(EvalOp::Eq, &[v2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::And, &[v0, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24is_5fvar_5flist(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListSetof, &[v6, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_core(EvalOp::Eq, &[v7, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::And, &[v5, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::And, &[v4, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24is_5frenaming_5frec(s, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5falpha_5fequiv(s, v10, v11, a0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5falpha_5fequiv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5falpha_5fequiv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_alpha_equiv"
pub fn eo__24eo_5fprog_5falpha_5fequiv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5falpha_5fequiv(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_139_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ealpha_5fequiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5falpha_5fequiv(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn cases_0_34_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_136_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_137_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_138_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_139_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fbeta_2dreduce(s: &mut Store, v8: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v8 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v8) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbeta_2dreduce(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24beta_5freduce(s, v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match requires_0_eo__24eo_5fprog_5fbeta_2dreduce(s, v8, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24eo_5fprog_5fbeta_2dreduce(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fbeta_2dreduce(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_beta-reduce"
pub fn eo__24eo_5fprog_5fbeta_2dreduce(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbeta_2dreduce(s, a0);
s.leave();
result
}
pub(super) fn case_140_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebeta_5freduce, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fbeta_2dreduce(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fquant_5fvar_5freordering(s: &mut Store, v22: Term, v23: Term, v12: Term, v9: Term, v19: Term) -> CheckResult<Term> {
if v22 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn more_1_eo__24eo_5fprog_5fquant_5fvar_5freordering(s: &mut Store, v16: Term, v9: Term, v12: Term, v19: Term) -> CheckResult<Option<Term>> {
if v16 != v9 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListMeq, &[v21, v12, v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_0_eo__24eo_5fprog_5fquant_5fvar_5freordering(s, v22, v23, v12, v9, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_5fvar_5freordering(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_1_eo__24eo_5fprog_5fquant_5fvar_5freordering(s, v16, v9, v12, v19)
}
pub(super) fn body_eo__24eo_5fprog_5fquant_5fvar_5freordering(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_5fvar_5freordering(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant_var_reordering"
pub fn eo__24eo_5fprog_5fquant_5fvar_5freordering(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_5fvar_5freordering(s, a0);
s.leave();
result
}
pub(super) fn case_141_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5fvar_5freordering, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_5fvar_5freordering(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5fexists_2delim(s: &mut Store, v29: Term, v32: Term, v12: Term, v9: Term) -> CheckResult<Option<Term>> {
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v36, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v34, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v33, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_0_eo__24eo_5fprog_5fexists_2delim(s: &mut Store, v19: Term, v12: Term, v20: Term, v9: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
if v23 != v12 { return Ok(None); }
let v25 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
if v27 != v9 { return Ok(None); }
let v29 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v9) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fexists_2delim(s, v29, v32, v12, v9)
}
pub(super) fn case_0_eo__24eo_5fprog_5fexists_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
more_0_eo__24eo_5fprog_5fexists_2delim(s, v19, v12, v20, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fexists_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fexists_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_exists-elim"
pub fn eo__24eo_5fprog_5fexists_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fexists_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_142_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2eexists_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fexists_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fquant_2dunused_2dvars(s: &mut Store, v23: Term, v24: Term, v11: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v23 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v23) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
pub(super) fn requires_0_eo__24get_5funused_5fvars(s: &mut Store, v15: Term, v16: Term, v5: Term, v11: Term) -> CheckResult<Term> {
if v15 != v16 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v15) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListSetof, &[v18, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListDiff, &[v17, v19, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_0_eo__24get_5funused_5fvars(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
if v10 != v4 { return Ok(None); }
if v8 != v2 { return Ok(None); }
let v12 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListSetof, &[v13, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListMinclude, &[v12, v14, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_0_eo__24get_5funused_5fvars(s, v15, v16, v5, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_1_eo__24get_5funused_5fvars(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if a1 != v2 { return Ok(None); }
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListSetof, &[v6, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24get_5funused_5fvars(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24get_5funused_5fvars(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24get_5funused_5fvars(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$get_unused_vars"
pub fn eo__24get_5funused_5fvars(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24get_5funused_5fvars(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_1_eo__24eo_5fprog_5fquant_2dunused_2dvars(s: &mut Store, v17: Term, v18: Term, v11: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24get_5funused_5fvars(s, v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v2, v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match requires_0_eo__24eo_5fprog_5fquant_2dunused_2dvars(s, v23, v24, v11, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
pub(super) fn more_2_eo__24eo_5fprog_5fquant_2dunused_2dvars(s: &mut Store, v17: Term, v18: Term, v11: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v31 = match requires_1_eo__24eo_5fprog_5fquant_2dunused_2dvars(s, v17, v18, v11, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_2dunused_2dvars(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Eq, &[v11, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Or, &[v14, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fquant_2dunused_2dvars(s, v17, v18, v11, v12, v9, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fquant_2dunused_2dvars(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_2dunused_2dvars(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant-unused-vars"
pub fn eo__24eo_5fprog_5fquant_2dunused_2dvars(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_2dunused_2dvars(s, a0);
s.leave();
result
}
pub(super) fn case_143_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5funused_5fvars, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_2dunused_2dvars(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_35_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_140_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_141_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_142_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_143_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_8_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_32_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_33_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_34_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_35_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s: &mut Store, v22: Term, v2: Term, v11: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v22 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
pub(super) fn case_0_eo__24mk_5fquant_5fmerge_5fprenex(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
if v4 != a0 { return Ok(None); }
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListConcat, &[v6, a2, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, v2, v7])))
}
pub(super) fn case_1_eo__24mk_5fquant_5fmerge_5fprenex(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.apply(a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn step_eo__24mk_5fquant_5fmerge_5fprenex(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24mk_5fquant_5fmerge_5fprenex(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fquant_5fmerge_5fprenex(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24mk_5fquant_5fmerge_5fprenex(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24mk_5fquant_5fmerge_5fprenex(s, a0, a1, a2) {
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
// EO program "$mk_quant_merge_prenex"
pub fn eo__24mk_5fquant_5fmerge_5fprenex(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(941), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fquant_5fmerge_5fprenex(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(941), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn requires_1_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s: &mut Store, v17: Term, v18: Term, v11: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24mk_5fquant_5fmerge_5fprenex(s, v11, v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match requires_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s, v22, v2, v11, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
pub(super) fn more_2_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s: &mut Store, v17: Term, v18: Term, v11: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v29 = match requires_1_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s, v17, v18, v11, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[v11, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_exists, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Eq, &[v11, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_core(EvalOp::Or, &[v14, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s, v17, v18, v11, v12, v9, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant-merge-prenex"
pub fn eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s, a0);
s.leave();
result
}
pub(super) fn case_144_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5fmerge_5fprenex, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_2dmerge_2dprenex(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand(s: &mut Store, v14: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v14 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_1_eo__24mk_5fquant_5fminiscope_5fand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$mk_quant_miniscope_and"
pub fn eo__24mk_5fquant_5fminiscope_5fand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(942), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fquant_5fminiscope_5fand(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(942), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fquant_5fminiscope_5fand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fquant_5fminiscope_5fand(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fquant_5fminiscope_5fand(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5fquant_5fminiscope_5fand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24mk_5fquant_5fminiscope_5fand(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24mk_5fquant_5fminiscope_5fand(s, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand(s, v14, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn body_eo__24eo_5fprog_5fquant_2dminiscope_2dand(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dand(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant-miniscope-and"
pub fn eo__24eo_5fprog_5fquant_2dminiscope_2dand(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_2dminiscope_2dand(s, a0);
s.leave();
result
}
pub(super) fn case_145_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5fminiscope_5fand, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_2dminiscope_2dand(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor(s: &mut Store, v14: Term, v15: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
pub(super) fn case_3_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v2 { return Ok(None); }
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_4_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_1_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$is_quant_miniscope_or"
pub fn eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(911), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(911), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
if v12 != v5 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v5, a0, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24is_5fquant_5fminiscope_5for(s, v15, v16, a0, v2, v9)
}
pub(super) fn case_1_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_3_eo__24is_5fquant_5fminiscope_5for(s, v19, v16, v5, a0, v2, v9)
}
pub(super) fn case_2_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_5_eo__24is_5fquant_5fminiscope_5for(s, v19, v5, v12, v16, v9, v2)
}
pub(super) fn cases_0_0_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24is_5fquant_5fminiscope_5for(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, v15: Term, v16: Term, a0: Term, v2: Term, v9: Term) -> CheckResult<Term> {
if v15 != v16 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v15) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match eo__24is_5fquant_5fminiscope_5for(s, a0, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
pub(super) fn more_1_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, v15: Term, v16: Term, a0: Term, v2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v18 = match requires_0_eo__24is_5fquant_5fminiscope_5for(s, v15, v16, a0, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn requires_2_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, v23: Term, v24: Term, a0: Term, v2: Term, v9: Term) -> CheckResult<Term> {
if v23 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v23) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v25 = match eo__24is_5fquant_5fminiscope_5for(s, a0, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn more_3_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, v19: Term, v16: Term, v5: Term, a0: Term, v2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v16 != v5 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v5, a0, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match requires_2_eo__24is_5fquant_5fminiscope_5for(s, v23, v24, a0, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn requires_4_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, v40: Term, v41: Term, v12: Term, v9: Term, v30: Term, v16: Term, v2: Term) -> CheckResult<Term> {
if v40 != v41 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v40) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v42 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v45, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match eo__24is_5fquant_5fminiscope_5for(s, v2, v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v51)
}
pub(super) fn more_6_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, v36: Term, v16: Term, v12: Term, v9: Term, v30: Term, v2: Term) -> CheckResult<Option<Term>> {
let v37 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v16, v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match requires_4_eo__24is_5fquant_5fminiscope_5for(s, v40, v41, v12, v9, v30, v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v52))
}
pub(super) fn more_5_eo__24is_5fquant_5fminiscope_5for(s: &mut Store, v19: Term, v5: Term, v12: Term, v16: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v27 { return Ok(None); }
let v28 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v34 { return Ok(None); }
if v33 != v5 { return Ok(None); }
if v23 != v12 { return Ok(None); }
let v35 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24is_5fquant_5fminiscope_5for(s, v36, v16, v12, v9, v30, v2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24is_5fquant_5fminiscope_5for(s, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match requires_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor(s, v14, v15, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn body_eo__24eo_5fprog_5fquant_2dminiscope_2dor(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dor(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant-miniscope-or"
pub fn eo__24eo_5fprog_5fquant_2dminiscope_2dor(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_2dminiscope_2dor(s, a0);
s.leave();
result
}
pub(super) fn case_146_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5fminiscope_5for, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_2dminiscope_2dor(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s: &mut Store, v62: Term, v12: Term, v19: Term, v61: Term, v16: Term, v59: Term) -> CheckResult<Term> {
let v63 = match s.apply(v62, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v61, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v65, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v59, v69) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v70)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s: &mut Store, v49: Term, v50: Term, v12: Term, v22: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v49 != v50 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v49) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v51 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v53, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v51, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s, v62, v12, v19, v61, v16, v59)
}
pub(super) fn more_3_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s: &mut Store, v36: Term, v19: Term, v26: Term, v12: Term, v16: Term, v22: Term) -> CheckResult<Option<Term>> {
if v36 != v19 { return Ok(None); }
let v41 = match s.unapply(v26) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v47 { return Ok(None); }
if v46 != v12 { return Ok(None); }
if v43 != v16 { return Ok(None); }
let v48 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v22, v12, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match requires_1_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s, v49, v50, v12, v22, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v71))
}
pub(super) fn more_2_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s: &mut Store, v21: Term, v23: Term, v2: Term, v22: Term, v12: Term, v19: Term, v16: Term) -> CheckResult<Option<Term>> {
if v21 != v23 { return Ok(None); }
let v24 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v25, v26)) = v24 else { return Ok(None); }
;
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != v22 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != v12 { return Ok(None); }
more_3_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s, v36, v19, v26, v12, v16, v22)
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s, v21, v23, v2, v22, v12, v19, v16)
}
pub(super) fn body_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant-miniscope-ite"
pub fn eo__24eo_5fprog_5fquant_2dminiscope_2dite(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_2dminiscope_2dite(s, a0);
s.leave();
result
}
pub(super) fn case_147_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5fminiscope_5fite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_2dminiscope_2dite(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_36_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_144_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_145_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_146_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_147_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s: &mut Store, v22: Term, v2: Term, v19: Term, v9: Term) -> CheckResult<Term> {
if v22 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v24, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v23, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn requires_0_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, v16: Term, v17: Term, a0: Term, v6: Term) -> CheckResult<Term> {
if v16 != v17 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v16) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24substitute_5fsimul_5frec(s, v18, v19, v23, v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
pub(super) fn more_1_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, v6: Term, v14: Term, a0: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v6, v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match requires_0_eo__24mk_5fquant_5fvar_5felim_5feq(s, v16, v17, a0, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn case_0_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
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
if v9 != a0 { return Ok(None); }
let v11 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fquant_5fvar_5felim_5feq(s, v6, v14, a0)
}
pub(super) fn more_2_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, v25: Term, v27: Term, v31: Term, v35: Term, v36: Term) -> CheckResult<Term> {
let v37 = match eo__24substitute_5fsimul_5frec(s, v25, v27, v31, v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v37)
}
pub(super) fn requires_3_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, v23: Term, v24: Term, v2: Term, a0: Term, v13: Term) -> CheckResult<Term> {
if v23 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v23) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v25 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_list(EvalOp::ListSingletonElim, &[v26, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fquant_5fvar_5felim_5feq(s, v25, v27, v31, v35, v36)
}
pub(super) fn more_4_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, a0: Term, v13: Term, v2: Term) -> CheckResult<Option<Term>> {
let v18 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, v13, v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match requires_3_eo__24mk_5fquant_5fvar_5felim_5feq(s, v23, v24, v2, a0, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v38))
}
pub(super) fn case_1_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
if v16 != a0 { return Ok(None); }
more_4_eo__24mk_5fquant_5fvar_5felim_5feq(s, a0, v13, v2)
}
pub(super) fn body_eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fquant_5fvar_5felim_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fquant_5fvar_5felim_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_quant_var_elim_eq"
pub fn eo__24mk_5fquant_5fvar_5felim_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fquant_5fvar_5felim_5feq(s, a0, a1);
s.leave();
result
}
pub(super) fn more_1_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s: &mut Store, v16: Term, v19: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v21 { return Ok(None); }
let v22 = match eo__24mk_5fquant_5fvar_5felim_5feq(s, v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s, v22, v2, v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_1_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s, v16, v19, v9, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant-var-elim-eq"
pub fn eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s, a0);
s.leave();
result
}
pub(super) fn case_148_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5fvar_5felim_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_2dvar_2delim_2deq(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s: &mut Store, v23: Term, v24: Term, v19: Term, v16: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v23 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v23) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v25, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
pub(super) fn requires_5_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, v9: Term, v10: Term, a0: Term, a1: Term, a3: Term, v3: Term) -> CheckResult<Term> {
if v9 != v10 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24substitute_5fsimul_5frec(s, v11, a3, v15, v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Eq, &[v21, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
pub(super) fn case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v6 != v8 { return Ok(None); }
let v9 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match requires_5_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, v9, v10, a0, a1, a3, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn requires_6_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, v1: Term, v2: Term, a0: Term, a1: Term, a3: Term, a4: Term) -> CheckResult<Term> {
if v1 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v3 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24substitute_5fsimul_5frec(s, v3, a3, v7, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[v13, a4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
pub(super) fn case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match requires_6_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, v1, v2, a0, a1, a3, a4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
// EO program "$is_quant_dt_split_conj"
pub fn eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(910), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(910), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_1_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, v19, v5, v16, v9, a0, a1, v2, a3)
}
pub(super) fn case_1_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v0 { return Ok(None); }
let v1 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListFind, &[v15, v10, v13]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, v16, v13, a3, a1, v10, v3, a0)
}
pub(super) fn requires_0_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, v22: Term, v23: Term, v16: Term, v9: Term, a0: Term, a1: Term, v2: Term, a3: Term) -> CheckResult<Term> {
if v22 != v23 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v22) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v24 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, a1, v2, a3, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
pub(super) fn more_1_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, v19: Term, v5: Term, v16: Term, v9: Term, a0: Term, a1: Term, v2: Term, a3: Term) -> CheckResult<Option<Term>> {
if v19 != v5 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListFind, &[v21, v16, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match requires_0_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, v22, v23, v16, v9, a0, a1, v2, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn requires_2_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, v23: Term, v24: Term, a1: Term, v13: Term, v10: Term, v3: Term, a0: Term, a3: Term) -> CheckResult<Term> {
if v23 != v24 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v23) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v25 = match s.apply(a1, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, v25, v26, a3, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
pub(super) fn requires_3_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, v16: Term, v17: Term, v13: Term, a3: Term, a1: Term, v10: Term, v3: Term, a0: Term) -> CheckResult<Term> {
if v16 != v17 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v16) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v18 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24contains_5fatomic_5fterm_5flist_5ffree_5frec(s, a3, v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match requires_2_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, v23, v24, a1, v13, v10, v3, a0, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
pub(super) fn more_4_eo__24is_5fquant_5fdt_5fsplit_5fconj(s: &mut Store, v16: Term, v13: Term, a3: Term, a1: Term, v10: Term, v3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match requires_3_eo__24is_5fquant_5fdt_5fsplit_5fconj(s, v16, v17, v13, a3, a1, v10, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn case_1_eo__24is_5fquant_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a4 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn requires_1_eo__24is_5fquant_5fdt_5fsplit(s: &mut Store, v2: Term, v7: Term, a0: Term, v5: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
if v2 != v7 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, v5, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
pub(super) fn case_2_eo__24is_5fquant_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match requires_1_eo__24is_5fquant_5fdt_5fsplit(s, v2, v7, a0, v5, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
// EO program "$is_quant_dt_split"
pub fn eo__24is_5fquant_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4];
match s.cached_program(ProgramId(909), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24is_5fquant_5fdt_5fsplit(s, a0, a1, a2, a3, a4);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(909), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24is_5fquant_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24is_5fquant_5fdt_5fsplit(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24is_5fquant_5fdt_5fsplit(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24is_5fquant_5fdt_5fsplit(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24is_5fquant_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24is_5fquant_5fdt_5fsplit_5fconj(s, a0, v5, a2, a3, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match requires_0_eo__24is_5fquant_5fdt_5fsplit(s, v14, v15, a0, v2, a2, a3, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn requires_0_eo__24is_5fquant_5fdt_5fsplit(s: &mut Store, v14: Term, v15: Term, a0: Term, v2: Term, a2: Term, a3: Term, v9: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match eo__24is_5fquant_5fdt_5fsplit(s, a0, v2, a2, a3, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s: &mut Store, v19: Term, v16: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5ftypeof(s, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24dt_5fget_5fconstructors(s, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24is_5fquant_5fdt_5fsplit(s, v19, v22, v16, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match requires_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s, v23, v24, v19, v16, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn case_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_1_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s, v19, v16, v9, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_quant-dt-split"
pub fn eo__24eo_5fprog_5fquant_2ddt_2dsplit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fquant_2ddt_2dsplit(s, a0);
s.leave();
result
}
pub(super) fn case_149_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2equant_5fdt_5fsplit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fquant_2ddt_2dsplit(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24mk_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$mk_dt_split"
pub fn eo__24mk_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(936), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdt_5fsplit(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(936), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5fsplit(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5fsplit(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24mk_5fdt_5fsplit(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_is, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24mk_5fdt_5fsplit(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_5fsplit(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24dt_5fget_5fconstructors(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24mk_5fdt_5fsplit(s, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_list(EvalOp::ListSingletonElim, &[v0, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5fprog_5fdt_5fsplit(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_5fsplit(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt_split"
pub fn eo__24eo_5fprog_5fdt_5fsplit(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_5fsplit(s, a0);
s.leave();
result
}
pub(super) fn case_150_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fsplit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_5fsplit(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dinst(s: &mut Store, v14: Term, v9: Term, v5: Term, v12: Term) -> CheckResult<Term> {
if v14 != v9 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_0_eo__24mk_5fdt_5finst_5ftuple_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$mk_dt_inst_tuple_rec"
pub fn eo__24mk_5fdt_5finst_5ftuple_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(935), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdt_5finst_5ftuple_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(935), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fdt_5finst_5ftuple_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5finst_5ftuple_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5finst_5ftuple_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24mk_5fdt_5finst_5ftuple_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_tuple_2eselect, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Add, &[a2, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24mk_5fdt_5finst_5ftuple_5frec(s, v2, a1, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24mk_5fdt_5finst_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_Tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24mk_5fdt_5finst_5ftuple_5frec(s, v9, a1, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_1_eo__24mk_5fdt_5finst_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24mk_5fdt_5finst_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5finst_5ftuple(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5finst_5ftuple(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_dt_inst_tuple"
pub fn eo__24mk_5fdt_5finst_5ftuple(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fdt_5finst_5ftuple(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24mk_5fdt_5finst_5fprem(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24mk_5fdt_5finst_5ftuple(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24mk_5fdt_5finst(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v11 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24mk_5fdt_5finst_5ftuple_5frec(s, v10, a2, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_1_eo__24mk_5fdt_5finst(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_UnitTuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24mk_5fdt_5finst_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(Next::Done(a2)))
}
pub(super) fn case_1_eo__24mk_5fdt_5finst_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(a2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, a1, v8])))
}
pub(super) fn step_eo__24mk_5fdt_5finst_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24mk_5fdt_5finst_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5finst_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24mk_5fdt_5finst_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24mk_5fdt_5finst_5frec(s, a0, a1, a2) {
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
// EO program "$mk_dt_inst_rec"
pub fn eo__24mk_5fdt_5finst_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(933), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdt_5finst_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(933), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_2_eo__24mk_5fdt_5finst(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24dt_5fget_5fselectors(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5fdt_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24dt_5fget_5fconstructors(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_list(EvalOp::ListFind, &[v3, v4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24assoc_5fnil_5fnth(s, v1, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24mk_5fdt_5finst_5frec(s, v0, a2, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24mk_5fdt_5finst(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5finst(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5finst(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24mk_5fdt_5finst(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_dt_inst"
pub fn eo__24mk_5fdt_5finst(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fdt_5finst(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_1_eo__24mk_5fdt_5finst_5fprem(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.destruct(Constructor::eo_is, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
if a1 != v2 { return Ok(None); }
let v5 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24mk_5fdt_5finst(s, v5, v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24mk_5fdt_5finst_5fprem(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5finst_5fprem(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5finst_5fprem(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_dt_inst_prem"
pub fn eo__24mk_5fdt_5finst_5fprem(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fdt_5finst_5fprem(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dinst(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24mk_5fdt_5finst_5fprem(s, v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_0_eo__24eo_5fprog_5fdt_2dinst(s, v14, v9, v5, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dinst(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dinst(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-inst"
pub fn eo__24eo_5fprog_5fdt_2dinst(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dinst(s, a0);
s.leave();
result
}
pub(super) fn case_151_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5finst, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dinst(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_37_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_148_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_149_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_150_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_151_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s: &mut Store, v16: Term, v2: Term, v8: Term, v9: Term) -> CheckResult<Term> {
if v16 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v16) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn more_1_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s: &mut Store, v16: Term, v2: Term, v8: Term, v9: Term) -> CheckResult<Option<Term>> {
let v21 = match requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s, v16, v2, v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24dt_5farg_5flist(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24dt_5fget_5fselectors_5fof_5fapp(s, v13, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListFind, &[v12, v14, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24assoc_5fnil_5fnth(s, v10, v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s, v16, v2, v8, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-collapse-selector"
pub fn eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s, a0);
s.leave();
result
}
pub(super) fn case_152_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fcollapse_5fselector, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dcollapse_2dselector(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s: &mut Store, v12: Term, v2: Term, v11: Term, v9: Term) -> CheckResult<Term> {
if v12 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v12) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v13 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_is, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.destruct(Constructor::eo_is, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match eo__24dt_5feq_5fcons(s, v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s, v12, v2, v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-collapse-tester"
pub fn eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s, a0);
s.leave();
result
}
pub(super) fn case_153_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fcollapse_5ftester, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dcollapse_2dtester(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s: &mut Store, v16: Term, v17: Term, v11: Term, v9: Term) -> CheckResult<Term> {
if v16 != v17 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v16) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_is, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v18, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
pub(super) fn more_1_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s: &mut Store, v16: Term, v11: Term, v9: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s, v16, v17, v11, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.destruct(Constructor::eo_is, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v12 { return Ok(None); }
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24dt_5fget_5fconstructors(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListLength, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s, v16, v11, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-collapse-tester-singleton"
pub fn eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s, a0);
s.leave();
result
}
pub(super) fn case_154_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fcollapse_5ftester_5fsingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dcollapse_2dtester_2dsingleton(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dcons_2deq(s: &mut Store, v16: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v16 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v16) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
pub(super) fn if_1_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
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
pub(super) fn if_2_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, condition: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
Some(false) => {
let v3 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_core(EvalOp::IsEq, &[a0, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_1_eo__24mk_5fdt_5fcons_5feq(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_3_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, v9: Term, v10: Term) -> CheckResult<Term> {
if v9 != v10 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v9) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
pub(super) fn case_2_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::IsEq, &[a0, v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_2_eo__24mk_5fdt_5fcons_5feq(s, v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match requires_3_eo__24mk_5fdt_5fcons_5feq(s, v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
// EO program "$mk_dt_cons_eq"
pub fn eo__24mk_5fdt_5fcons_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(930), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5fdt_5fcons_5feq(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(930), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5fcons_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5fcons_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24mk_5fdt_5fcons_5feq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fdt_5fcons_5feq(s, v14, v17, v2, v9)
}
pub(super) fn case_1_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24mk_5fdt_5fcons_5feq(s, v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListConcat, &[v6, v7, v14]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24mk_5fdt_5fcons_5feq(s: &mut Store, v14: Term, v17: Term, v2: Term, v9: Term) -> CheckResult<Option<Term>> {
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24mk_5fdt_5fcons_5feq(s, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dcons_2deq(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24mk_5fdt_5fcons_5feq(s, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListSingletonElim, &[v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match requires_0_eo__24eo_5fprog_5fdt_2dcons_2deq(s, v16, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dcons_2deq(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dcons_2deq(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-cons-eq"
pub fn eo__24eo_5fprog_5fdt_2dcons_2deq(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dcons_2deq(s, a0);
s.leave();
result
}
pub(super) fn case_155_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fcons_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dcons_2deq(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_38_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_152_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_153_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_154_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_155_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s: &mut Store, condition: Term, v12: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match eo__24eo_5ftypeof(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24are_5fdistinct_5fterms_5ftype(s, v12, v9, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_1_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s: &mut Store, v19: Term, v20: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v19 != v20 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v19) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
pub(super) fn more_2_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s: &mut Store, v19: Term, v12: Term, v9: Term) -> CheckResult<Option<Term>> {
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match requires_1_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s, v19, v20, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v14 { return Ok(None); }
let v15 = match s.builtin_core(EvalOp::Eq, &[v12, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match if_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s, v15, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s, v19, v12, v9)
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-cons-eq-clash"
pub fn eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s, a0);
s.leave();
result
}
pub(super) fn case_156_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fcons_5feq_5fclash, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dcons_2deq_2dclash(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dcycle(s: &mut Store, v17: Term, v18: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn more_1_eo__24eo_5fprog_5fdt_2dcycle(s: &mut Store, v9: Term, v12: Term, v15: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24dt_5ffind_5fcycle(s, v9, v12, v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match requires_0_eo__24eo_5fprog_5fdt_2dcycle(s, v17, v18, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dcycle(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v14 { return Ok(None); }
let v15 = match eo__24is_5fcons_5fapp(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fdt_2dcycle(s, v9, v12, v15, v16)
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dcycle(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dcycle(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-cycle"
pub fn eo__24eo_5fprog_5fdt_2dcycle(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dcycle(s, a0);
s.leave();
result
}
pub(super) fn case_157_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fcycle, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dcycle(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s: &mut Store, v7: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v7 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v7) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
pub(super) fn more_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s: &mut Store, v5: Term, v2: Term, v24: Term) -> CheckResult<Term> {
let v25 = match eo__24dt_5fcollapse_5fupdater_5frhs(s, v5, v2, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
pub(super) fn if_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s: &mut Store, condition: Term, v5: Term, v7: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v5)
}
Some(false) => {
let v13 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24dt_5fget_5fselectors_5fof_5fapp(s, v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListLength, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24dt_5fget_5fselectors_5fof_5fapp(s, v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_list(EvalOp::ListFind, &[v17, v19, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Neg, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Add, &[v16, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::Add, &[v22, v23]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s, v5, v2, v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24dt_5fget_5fselectors_5fof_5fapp(s, v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_list(EvalOp::ListFind, &[v8, v10, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::IsNeg, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match if_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s, v12, v5, v7, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24tuple_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_2_eo__24tuple_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$tuple_collapse_updater_rhs"
pub fn eo__24tuple_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1099), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24tuple_5fcollapse_5fupdater_5frhs(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1099), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24tuple_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24tuple_5fcollapse_5fupdater_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24tuple_5fcollapse_5fupdater_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24tuple_5fcollapse_5fupdater_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24tuple_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Add, &[a2, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24tuple_5fcollapse_5fupdater_5frhs(s, v2, a1, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v8 = match eo__24tuple_5fcollapse_5fupdater_5frhs(s, v5, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_dt_collapse_updater_rhs"
pub fn eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24mk_5fdt_5fcollapse_5fupdater_5frhs(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match requires_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s, v7, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-collapse-updater"
pub fn eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s, a0);
s.leave();
result
}
pub(super) fn case_158_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fcollapse_5fupdater, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dcollapse_2dupdater(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fdt_2dupdater_2delim(s: &mut Store, v15: Term, v16: Term, v11: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v15 != v16 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v15) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v17, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v21)
}
pub(super) fn requires_0_eo__24mk_5fdt_5fupdater_5felim_5fconc(s: &mut Store, v15: Term, a1: Term) -> CheckResult<Term> {
if v15 != a1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v15) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
pub(super) fn requires_0_eo__24mk_5fdt_5fupdater_5felim_5frhs(s: &mut Store, v10: Term, v11: Term, v7: Term, v5: Term, v2: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if v10 != v11 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v10) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v12 = match s.construct(Constructor::eo_update, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24eo_5fdt_5fconstructors(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24dt_5fget_5fconstructors(s, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_list(EvalOp::ListFind, &[v18, v20, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24assoc_5fnil_5fnth(s, v15, v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24dt_5fupdater_5felim_5frhs(s, v14, a2, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
pub(super) fn case_0_eo__24mk_5fdt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListFind, &[v8, a2, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match requires_0_eo__24mk_5fdt_5fupdater_5felim_5frhs(s, v10, v11, v7, v5, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_2_eo__24tuple_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_tuple_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
// EO program "$tuple_updater_elim_rhs"
pub fn eo__24tuple_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1101), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24tuple_5fupdater_5felim_5frhs(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1101), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24tuple_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24tuple_5fupdater_5felim_5frhs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24tuple_5fupdater_5felim_5frhs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24tuple_5fupdater_5felim_5frhs(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24tuple_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.destruct(Constructor::eo_tuple_2eselect, v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v15 else { return Ok(None); }
;
let v16 = fields[0];
if v16 != v7 { return Ok(None); }
let v17 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_tuple_2eupdate, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24tuple_5fupdater_5felim_5frhs(s, v19, v5, v2, v10, v18)
}
pub(super) fn case_1_eo__24tuple_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_tuple_2eupdate, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24tuple_5fupdater_5felim_5frhs(s, v19, v2, v10, v17)
}
pub(super) fn more_0_eo__24tuple_5fupdater_5felim_5frhs(s: &mut Store, v19: Term, v5: Term, v2: Term, v10: Term, v18: Term) -> CheckResult<Option<Term>> {
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24tuple_5fupdater_5felim_5frhs(s, v21, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn more_1_eo__24tuple_5fupdater_5felim_5frhs(s: &mut Store, v19: Term, v2: Term, v10: Term, v17: Term) -> CheckResult<Option<Term>> {
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24tuple_5fupdater_5felim_5frhs(s, v20, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v17, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_1_eo__24mk_5fdt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v8 { return Ok(None); }
let v9 = match s.construct(Constructor::eo_tuple_2eupdate, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24tuple_5fupdater_5felim_5frhs(s, v11, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24mk_5fdt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5fupdater_5felim_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5fupdater_5felim_5frhs(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_dt_updater_elim_rhs"
pub fn eo__24mk_5fdt_5fupdater_5felim_5frhs(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fdt_5fupdater_5felim_5frhs(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24mk_5fdt_5fupdater_5felim_5fconc(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v8 = match s.construct(Constructor::eo_tuple_2eupdate, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_tuple, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24dt_5fget_5fselectors(s, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24mk_5fdt_5fupdater_5felim_5frhs(s, v10, v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match requires_0_eo__24mk_5fdt_5fupdater_5felim_5fconc(s, v15, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn requires_1_eo__24mk_5fdt_5fupdater_5felim_5fconc(s: &mut Store, v28: Term, v13: Term) -> CheckResult<Term> {
if v28 != v13 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v28) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v29 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
pub(super) fn more_2_eo__24mk_5fdt_5fupdater_5felim_5fconc(s: &mut Store, v7: Term, v5: Term, v2: Term, v22: Term, v13: Term) -> CheckResult<Option<Term>> {
let v23 = match s.construct(Constructor::eo_update, &[v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24dt_5fget_5fselectors(s, v26, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24mk_5fdt_5fupdater_5felim_5frhs(s, v25, v22, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match requires_1_eo__24mk_5fdt_5fupdater_5felim_5fconc(s, v28, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn case_1_eo__24mk_5fdt_5fupdater_5felim_5fconc(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
let v21 = match s.destruct(Constructor::eo_is, v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v21 else { return Ok(None); }
;
let v22 = fields[0];
if v20 != v5 { return Ok(None); }
if v10 != v5 { return Ok(None); }
more_2_eo__24mk_5fdt_5fupdater_5felim_5fconc(s, v7, v5, v2, v22, v13)
}
pub(super) fn body_eo__24mk_5fdt_5fupdater_5felim_5fconc(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24mk_5fdt_5fupdater_5felim_5fconc(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24mk_5fdt_5fupdater_5felim_5fconc(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_dt_updater_elim_conc"
pub fn eo__24mk_5fdt_5fupdater_5felim_5fconc(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fdt_5fupdater_5felim_5fconc(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24mk_5fdt_5fupdater_5felim_5fconc(s, v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match requires_0_eo__24eo_5fprog_5fdt_2dupdater_2delim(s, v15, v16, v11, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn body_eo__24eo_5fprog_5fdt_2dupdater_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fdt_2dupdater_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_dt-updater-elim"
pub fn eo__24eo_5fprog_5fdt_2dupdater_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fdt_2dupdater_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_159_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2edt_5fupdater_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fdt_2dupdater_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_39_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_156_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_157_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_158_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_159_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_9_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_36_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_37_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_38_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_39_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v4 = match s.literal(Lit::Rational(v3)) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v8 = match s.literal(Lit::Rational(v7)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-div-total-zero-real"
pub fn eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal(s, a0);
s.leave();
result
}
pub(super) fn case_160_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dreal(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v7 = match s.literal(Lit::Rational(v6)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-div-total-zero-int"
pub fn eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint(s, a0);
s.leave();
result
}
pub(super) fn case_161_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fdiv_5ftotal_5fzero_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dzero_2dint(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s: &mut Store, v4: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_div, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
if v14 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s, v4, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-div-total"
pub fn eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_162_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-div-total-one"
pub fn eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done(s, a0);
s.leave();
result
}
pub(super) fn case_163_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2done(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_40_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_160_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_161_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_162_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_163_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-div-total-zero"
pub fn eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero(s, a0);
s.leave();
result
}
pub(super) fn case_164_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dzero(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s: &mut Store, v25: Term, v27: Term, v23: Term, v22: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v23, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v22, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s: &mut Store, v4: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s, v25, v27, v23, v22)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s, v4, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-div-total-neg"
pub fn eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_165_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dneg(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s: &mut Store, v4: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v22, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
if v14 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s, v4, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-mod-total"
pub fn eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_166_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fmod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-mod-total-one"
pub fn eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done(s, a0);
s.leave();
result
}
pub(super) fn case_167_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2done(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_41_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_164_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_165_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_166_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_167_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-mod-total-zero"
pub fn eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero(s, a0);
s.leave();
result
}
pub(super) fn case_168_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fzero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dzero(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s: &mut Store, v22: Term, v27: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v22, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s: &mut Store, v4: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s, v22, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s, v4, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-mod-total-neg"
pub fn eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_169_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fmod_5ftotal_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5farith_2dint_2dmod_2dtotal_2dneg(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_div_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-div-total-over-mod"
pub fn eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod(s, a0, a1);
s.leave();
result
}
pub(super) fn case_170_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fdiv_5ftotal_5fover_5fmod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dint_2ddiv_2dtotal_2dover_2dmod(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2delim_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2delim_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2delim_2dgt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-elim-gt"
pub fn eo__24eo_5fprog_5farith_2delim_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2delim_2dgt(s, a0, a1);
s.leave();
result
}
pub(super) fn case_171_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5felim_5fgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2delim_2dgt(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_42_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_168_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_169_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_170_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_171_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2delim_2dlt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2delim_2dlt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2delim_2dlt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-elim-lt"
pub fn eo__24eo_5fprog_5farith_2delim_2dlt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2delim_2dlt(s, a0, a1);
s.leave();
result
}
pub(super) fn case_172_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5felim_5flt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2delim_2dlt(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s: &mut Store, v11: Term, v8: Term, v6: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v6, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s, v11, v8, v6, v4)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-elim-int-gt"
pub fn eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s, a0, a1);
s.leave();
result
}
pub(super) fn case_173_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5felim_5fint_5fgt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2delim_2dint_2dgt(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s: &mut Store, v11: Term, v8: Term, v6: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v6, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s, v11, v8, v6, v4)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-elim-int-lt"
pub fn eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s, a0, a1);
s.leave();
result
}
pub(super) fn case_174_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5felim_5fint_5flt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2delim_2dint_2dlt(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2delim_2dleq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2delim_2dleq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2delim_2dleq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-elim-leq"
pub fn eo__24eo_5fprog_5farith_2delim_2dleq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2delim_2dleq(s, a0, a1);
s.leave();
result
}
pub(super) fn case_175_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5felim_5fleq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2delim_2dleq(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_43_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_172_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_173_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_174_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_175_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_10_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_40_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_41_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_42_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_43_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dleq_2dnorm(s: &mut Store, v10: Term, v11: Term, v9: Term, v7: Term, v5: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v9, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v7, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v5, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v4, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dleq_2dnorm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dleq_2dnorm(s, v10, v11, v9, v7, v5, v4)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dleq_2dnorm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dleq_2dnorm(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-leq-norm"
pub fn eo__24eo_5fprog_5farith_2dleq_2dnorm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dleq_2dnorm(s, a0, a1);
s.leave();
result
}
pub(super) fn case_176_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fleq_5fnorm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dleq_2dnorm(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dgeq_2dtighten(s: &mut Store, v11: Term, v10: Term, v8: Term, v6: Term) -> CheckResult<Option<Term>> {
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v6, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dgeq_2dtighten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dgeq_2dtighten(s, v11, v10, v8, v6)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dgeq_2dtighten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dgeq_2dtighten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-geq-tighten"
pub fn eo__24eo_5fprog_5farith_2dgeq_2dtighten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dgeq_2dtighten(s, a0, a1);
s.leave();
result
}
pub(super) fn case_177_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fgeq_5ftighten, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dgeq_2dtighten(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s: &mut Store, v4: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v4, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s, v4, v11)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-geq-norm1-int"
pub fn eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s, a0, a1);
s.leave();
result
}
pub(super) fn case_178_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fgeq_5fnorm1_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dint(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s: &mut Store, v4: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v4, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match Rational::from_integers(&Integer::from(0u32), &Integer::from(1u32)) { Some(q) => q, None => return Err(CheckError::InvalidNative) };
let v11 = match s.literal(Lit::Rational(v10)) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s, v4, v12)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-geq-norm1-real"
pub fn eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s, a0, a1);
s.leave();
result
}
pub(super) fn case_179_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fgeq_5fnorm1_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2dgeq_2dnorm1_2dreal(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_44_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_176_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_177_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_178_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_179_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s: &mut Store, v11: Term, a0: Term, a1: Term, v10: Term, v9: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v4, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s, v11, a0, a1, v10, v9, v4)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-eq-elim-real"
pub fn eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s, a0, a1);
s.leave();
result
}
pub(super) fn case_180_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5feq_5felim_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2deq_2delim_2dreal(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint(s: &mut Store, v11: Term, a0: Term, a1: Term, v10: Term, v9: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v4, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint(s, v11, a0, a1, v10, v9, v4)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2deq_2delim_2dint(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2deq_2delim_2dint(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-eq-elim-int"
pub fn eo__24eo_5fprog_5farith_2deq_2delim_2dint(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2deq_2delim_2dint(s, a0, a1);
s.leave();
result
}
pub(super) fn case_181_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5feq_5felim_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2deq_2delim_2dint(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-to-int-elim-to-real"
pub fn eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal(s, a0);
s.leave();
result
}
pub(super) fn case_182_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fto_5fint_5felim_5fto_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dto_2dint_2delim_2dto_2dreal(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_is_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-is-int-elim-to-real"
pub fn eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal(s, a0);
s.leave();
result
}
pub(super) fn case_183_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fis_5fint_5felim_5fto_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dis_2dint_2delim_2dto_2dreal(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_45_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_180_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_181_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_182_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_183_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s: &mut Store, v4: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v4, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__2f, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s, v4, v11)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-div-int-to-real"
pub fn eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s, a0, a1);
s.leave();
result
}
pub(super) fn case_184_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fdiv_5fint_5fto_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2ddiv_2dint_2dto_2dreal(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s: &mut Store, v4: Term, v11: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v4, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__2f_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s, v4, v11)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-div-total-int-to-real"
pub fn eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s, a0, a1);
s.leave();
result
}
pub(super) fn case_185_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fdiv_5ftotal_5fint_5fto_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5farith_2ddiv_2dtotal_2dint_2dto_2dreal(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s: &mut Store, v27: Term, a0: Term, v25: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v29))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s: &mut Store, v4: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v18, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s, v27, a0, v25)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
if v14 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s, v4, a1, a0)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-mod-over-mod-1"
pub fn eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_186_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2d1(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_2_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s: &mut Store, v39: Term, a0: Term, v30: Term) -> CheckResult<Option<Term>> {
let v40 = match s.apply(v39, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v30, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s: &mut Store, v19: Term, v27: Term, a0: Term, v18: Term, a2: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v19, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v18, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_list(EvalOp::ListConcat, &[v33, a1, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListSingletonElim, &[v32, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v31, v38) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s, v39, a0, v30)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s: &mut Store, v4: Term, a2: Term, a0: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_list(EvalOp::ListConcat, &[v20, a1, v26]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s, v19, v27, a0, v18, a2, a3, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v14 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s, v4, a2, a0, a3, a1)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-mod-over-mod"
pub fn eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_12_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5farith_2dmod_2dover_2dmod(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_187_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmod_5fover_5fmod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_12_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_46_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_184_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_185_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_186_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_187_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s: &mut Store, v39: Term, a0: Term, v30: Term) -> CheckResult<Option<Term>> {
let v40 = match s.apply(v39, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v30, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s: &mut Store, v19: Term, v27: Term, a0: Term, v18: Term, a2: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v19, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v18, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_list(EvalOp::ListConcat, &[v33, a1, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListSingletonElim, &[v32, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v31, v38) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s, v39, a0, v30)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s: &mut Store, v4: Term, a2: Term, a0: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_list(EvalOp::ListConcat, &[v20, a1, v26]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s, v19, v27, a0, v18, a2, a3, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v14 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s, v4, a2, a0, a3, a1)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-mod-over-mod-mult"
pub fn eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_13_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5farith_2dmod_2dover_2dmod_2dmult(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_188_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fmod_5fover_5fmod_5fmult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_13_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s: &mut Store, v29: Term, a1: Term, v25: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v29, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v25, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v31, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s: &mut Store, v18: Term, a1: Term, v11: Term, v4: Term, a0: Term) -> CheckResult<Option<Term>> {
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a1 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s, v29, a1, v25)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v19 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s, v18, a1, v11, v4, a0)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-eq-conflict"
pub fn eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_189_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5feq_5fconflict, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5farith_2dint_2deq_2dconflict(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_3_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s: &mut Store, a0: Term, a2: Term, v60: Term) -> CheckResult<Option<Term>> {
let v61 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v60, v63) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v64))
}
pub(super) fn more_2_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s: &mut Store, v49: Term, v51: Term, v50: Term, v47: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v49 != v51 { return Ok(None); }
let v52 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v52 { return Ok(None); }
let v53 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v47 != v53 { return Ok(None); }
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v54, v59) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s, a0, a2, v60)
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s: &mut Store, v32: Term, a2: Term, v29: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
if v32 != a2 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a1 { return Ok(None); }
let v45 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s, v49, v51, v50, v47, a0, a1, a2)
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s: &mut Store, v18: Term, a1: Term, v11: Term, v4: Term, a4: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_to_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a1 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
more_1_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s, v32, a2, v29, a1, a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_to_5freal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s, v18, a1, v11, v4, a4, a2, a0)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-int-geq-tighten"
pub fn eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_14_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5farith_2dint_2dgeq_2dtighten(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_190_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fint_5fgeq_5ftighten, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_14_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2ddivisible_2delim(s: &mut Store, v27: Term, v22: Term) -> CheckResult<Option<Term>> {
let v28 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v22, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2ddivisible_2delim(s: &mut Store, v4: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_divisible, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_mod_5ftotal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2ddivisible_2delim(s, v27, v22)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2ddivisible_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
if v14 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5farith_2ddivisible_2delim(s, v4, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2ddivisible_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2ddivisible_2delim(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-divisible-elim"
pub fn eo__24eo_5fprog_5farith_2ddivisible_2delim(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2ddivisible_2delim(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_191_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fdivisible_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5farith_2ddivisible_2delim(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn cases_0_47_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_188_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_189_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_190_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_191_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_11_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_44_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_45_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_46_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_47_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_2_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_8_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_9_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_10_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_11_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dabs_2deq(s: &mut Store, v8: Term, v23: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v8, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn more_0_eo__24eo_5fprog_5farith_2dabs_2deq(s: &mut Store, v11: Term, a1: Term, v9: Term, a0: Term, v8: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eoo_5f_2d_2e2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v14, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v13, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5farith_2dabs_2deq(s, v8, v23)
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dabs_2deq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_abs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v0, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5farith_2dabs_2deq(s, v11, a1, v9, a0, v8)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dabs_2deq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dabs_2deq(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-abs-eq"
pub fn eo__24eo_5fprog_5farith_2dabs_2deq(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dabs_2deq(s, a0, a1);
s.leave();
result
}
