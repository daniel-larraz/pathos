//! Generated functions, module 0 of 1.
#[allow(unused_imports)]
use super::*;
use crate::*;
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
pub(super) fn case_0_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBoolean, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fNumeral(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fNumeral(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fNumeral(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_Numeral"
pub fn eo__24eo_5flit_5ftype_5fNumeral(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fNumeral(s, a0);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fNumeral, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5flit_5ftype_5fNumeral(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fRational(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fRational(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fRational(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_Rational"
pub fn eo__24eo_5flit_5ftype_5fRational(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fRational(s, a0);
s.leave();
result
}
pub(super) fn case_2_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fRational, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fRational, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5flit_5ftype_5fRational(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fString(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fString(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fString(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_String"
pub fn eo__24eo_5flit_5ftype_5fString(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fString(s, a0);
s.leave();
result
}
pub(super) fn case_3_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fString, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fString, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5flit_5ftype_5fString(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn cases_0_0_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5flit_5ftype_5fBinary(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.builtin_core(EvalOp::Length, &[a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5flit_5ftype_5fBinary(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5flit_5ftype_5fBinary(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_lit_type_Binary"
pub fn eo__24eo_5flit_5ftype_5fBinary(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5flit_5ftype_5fBinary(s, a0);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBinary, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fBinary, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5flit_5ftype_5fBinary(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_5_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fString, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(v2))
}
pub(super) fn case_6_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDatatypeType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$eo_dd_lookup"
pub fn eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(6), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdd_5flookup(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(6), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24eo_5fdd_5flookup(s, v4, v2, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fdd_5flookup(s: &mut Store, condition: Term, v2: Term, a0: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v5 = match eo__24eo_5fdd_5flookup(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$eo_dtc_resolve"
pub fn eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(13), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdtc_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(13), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fDatatypeTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.construct(Constructor::eo__24emb_5fDatatypeType, &[v4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fedtc_2econs, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24eo_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fedtc_2econs, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$eo_dt_resolve"
pub fn eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(10), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdt_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(10), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fdtc_5fresolve(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fdt_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24eo_5fdd_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5fdt_5fresolve(s, v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fdd_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fdd_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_dd_resolve"
pub fn eo__24eo_5fdd_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdd_5fresolve(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
Ok(Some(Next::Done(a0)))
}
pub(super) fn case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([a0, v2, v4])))
}
// EO program "$eo_typeof_dt_cons_rec"
pub fn eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(53), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(53), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) {
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
pub(super) fn step_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24eo_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, a0, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fDtcAppType, &[v4, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_7_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.construct(Constructor::eo__24emb_5fDatatypeType, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fdd_5fresolve(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof_5fdt_5fcons_5frec(s, v4, v5, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_1_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v9, v10, v8])))
}
pub(super) fn case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([v2, v4, a2])))
}
pub(super) fn step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2) {
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
// EO program "$eo_typeof_dt_sel_return"
pub fn eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(54), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(54), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_8_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtSel, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match eo__24eo_5fdd_5fresolve(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5ftypeof_5fdt_5fsel_5freturn(s, v5, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fDatatypeType, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fFunType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_9_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUSort, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_10_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUConst, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(v2))
}
pub(super) fn case_11_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn cases_0_2_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5ffun_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5ffun_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5ffun_5ftype(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_fun_type"
pub fn eo__24eo_5ftypeof_5ffun_5ftype(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5ffun_5ftype(s, a0, a1);
s.leave();
result
}
pub(super) fn case_13_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_14_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_15_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_16_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fFunType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_17_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_18_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fBitVec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fBitVec(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fBitVec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_BitVec"
pub fn eo__24eo_5ftypeof_5fBitVec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fBitVec(s, a0);
s.leave();
result
}
pub(super) fn case_20_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fSeq(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fType, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fSeq(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fSeq(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_Seq"
pub fn eo__24eo_5ftypeof_5fSeq(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fSeq(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fnot(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5ftypeof_5fnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fnot(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_not"
pub fn eo__24eo_5ftypeof_5fnot(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fnot(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5ftypeof_5fand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fand(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_and"
pub fn eo__24eo_5ftypeof_5fand(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fand(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5f_3d(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_="
pub fn eo__24eo_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5f_3d(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_0_eo__24eo_5ftypeof_5fapply(s: &mut Store, v5: Term, a1: Term, v2: Term) -> CheckResult<Term> {
if v5 != a1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v5) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(v2)
}
pub(super) fn case_0_eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.is_node(v4, Some(Constructor::eo__24emb_5fFunType)) { Ok(v) => v, Err(e) => return Err(e) };
if !v6 { return Ok(None); }
let v7 = match requires_0_eo__24eo_5ftypeof_5fapply(s, v5, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn requires_1_eo__24eo_5ftypeof_5fapply(s: &mut Store, v1: Term, a1: Term, v2: Term) -> CheckResult<Term> {
if v1 != a1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(v2)
}
pub(super) fn case_1_eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match requires_1_eo__24eo_5ftypeof_5fapply(s, v1, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_typeof_apply"
pub fn eo__24eo_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5ftypeof_5fapply(s, a0, a1);
s.leave();
result
}
// EO program "$eo_typeof"
pub fn eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_type(TypeCacheKind::Eunoia, cache_args[0]) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5ftypeof(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_type(TypeCacheKind::Eunoia, cache_args[0], value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_1_0_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_1_1_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_12_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.is_node(v4, Some(Constructor::eo__24emb_5fFunType)) { Ok(v) => v, Err(e) => return Err(e) };
if !v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5ffun_5ftype(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_19_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fBitVec(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_21_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fSeq(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_22_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fnot(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_23_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_24_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5fand(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_25_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5ftypeof(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5ftypeof_5f_3d(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_26_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24eo_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5ftypeof_5fapply(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_3_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_4_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_18_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_19_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_5_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_20_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_21_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_22_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_23_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_6_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_24_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_25_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_26_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24eo_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_5_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_6_eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
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
pub(super) fn case_0_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_3_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_is_closed_rec"
pub fn eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(21), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fis_5fclosed_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(21), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24eo_5fis_5fclosed_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
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
Ok(Some(v15))
}
pub(super) fn case_2_eo__24eo_5fis_5fclosed_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24eo_5fis_5fclosed_5frec(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fis_5fclosed_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
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
pub(super) fn more_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v10: Term, v12: Term) -> CheckResult<Option<Term>> {
let v13 = match eo__24eo_5fprog_5fcontra(s, v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
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
more_0_eo__24eo_5fcmd_5fstep_5fproven(s, v10, v12)
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
pub(super) fn case_1_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_2_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_0_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_nil"
pub fn eo__24eo_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fnil(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fmk_5fpremise_5flist(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5fnil(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_0_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fis_5flist_5fnil(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_is_list_nil"
pub fn eo__24eo_5fis_5flist_5fnil(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fis_5flist_5fnil(s, a0, a1);
s.leave();
result
}
// The list operators. They ask generated functions whether a term ends a
// list and for the empty list of a type (`$eo_is_list_nil`, `$eo_nil`,
// `$eo_typeof`), so this is not part of the runtime that the generated
// code rests on: the generator puts it among the generated functions,
// after those three and before the functions that use a list operator.
impl Store {
    /// Ethos-style primitive evaluation over already evaluated values:
    /// any operator. (Generated code calls `builtin_core` or
    /// `builtin_list`, whichever its operator needs.)
    pub fn builtin(&mut self, op: EvalOp, args: &[Term]) -> CheckResult<Term> {
        if op.is_list_op() {
            self.builtin_list(op, args)
        } else {
            self.builtin_core(op, args)
        }
    }
    /// A list operator.
    pub(crate) fn builtin_list(&mut self, op: EvalOp, args: &[Term]) -> CheckResult<Term> {
        if !Self::takes(op, args.len()) {
            return Ok(self.stuck());
        }
        self.check_handles(args)?;
        if self.any_stuck(args) {
            return Ok(self.stuck());
        }
        self.list_builtin(op, args)
    }
    /// Whether the list constructor `f` nests to the left.
    fn is_left_assoc(&self, f: Term) -> CheckResult<bool> {
        Ok(match self.view(f)? {
            TermData::Node(c, _) => c.is_left_assoc(),
            _ => false,
        })
    }
    /// The next element of a list of `f` and the rest of the list, or
    /// `None` where the list of applications of `f` ends. `count` is the
    /// number of elements taken so far.
    fn list_step(
        &self,
        f: Term,
        left: bool,
        list: Term,
        count: usize,
    ) -> CheckResult<Option<(Term, Term)>> {
        let Some((g, b)) = self.unapply(list)? else {
            return Ok(None);
        };
        let Some((head, a)) = self.unapply(g)? else {
            return Ok(None);
        };
        if f != head {
            return Ok(None);
        }
        if count as u64 >= self.limits.calls {
            return Err(CheckError::Limit);
        }
        Ok(Some(if left { (b, a) } else { (a, b) }))
    }
    /// The elements of a list of `f`, and where its applications of `f` end.
    fn list_elements(&self, f: Term, left: bool, list: Term) -> CheckResult<(Vec<Term>, Term)> {
        let mut out = Vec::new();
        let mut list = list;
        let mut more = true;
        while more {
            match self.list_step(f, left, list, out.len())? {
                Some((element, rest)) => {
                    out.push(element);
                    list = rest;
                }
                None => more = false,
            }
        }
        Ok((out, list))
    }
    fn list_parts(&mut self, f: Term, list: Term) -> CheckResult<Option<(Vec<Term>, Term)>> {
        let left = self.is_left_assoc(f)?;
        let (out, list) = self.list_elements(f, left, list)?;
        let is_nil = generated::eo__24eo_5fis_5flist_5fnil(self, f, list)?;
        match self.boolean_value(is_nil, false)? {
            Some(true) => {}
            _ => return Ok(None),
        }
        Ok(Some((out, list)))
    }
    /// The list of `f` with the element `e` before `tail`.
    fn list_cons(&mut self, f: Term, left: bool, e: Term, tail: Term) -> CheckResult<Term> {
        let first = self.apply(f, if left { tail } else { e })?;
        self.apply(first, if left { e } else { tail })
    }
    fn list_build(&mut self, f: Term, elems: &[Term], nil: Term) -> CheckResult<Term> {
        let left = self.is_left_assoc(f)?;
        let mut list = nil;
        let mut i = elems.len();
        while i > 0 {
            i -= 1;
            list = self.list_cons(f, left, elems[i], list)?;
        }
        Ok(list)
    }
    fn list_builtin(&mut self, op: EvalOp, a: &[Term]) -> CheckResult<Term> {
        let f = a[0];
        match op {
            EvalOp::Nil => generated::eo__24eo_5fnil(self, f, a[1]),
            EvalOp::ListRepeat => self.list_repeat(f, a[1], a[2]),
            EvalOp::Cons => self.list_cons_op(f, a[1], a[2]),
            EvalOp::ListConcat => self.list_concat(f, a[1], a[2]),
            EvalOp::ListMinclude | EvalOp::ListMeq => self.list_inclusion(op, f, a[1], a[2]),
            EvalOp::ListDiff | EvalOp::ListInter => self.list_selection(op, f, a[1], a[2]),
            _ => self.list_of_one(op, f, a),
        }
    }
    /// The list of `f` that is empty for elements of the type of `x`.
    fn list_nil_for(&mut self, f: Term, x: Term) -> CheckResult<Term> {
        let ty = generated::eo__24eo_5ftypeof(self, x)?;
        generated::eo__24eo_5fnil(self, f, ty)
    }
    fn list_repeat(&mut self, f: Term, x: Term, count: Term) -> CheckResult<Term> {
        let Some(n) = self.object_index(count)? else {
            return Ok(self.stuck());
        };
        if u64::from(n) > self.limits.calls {
            return Err(CheckError::Limit);
        }
        let nil = self.list_nil_for(f, x)?;
        let elems = vec![x; n as usize];
        self.list_build(f, &elems, nil)
    }
    fn list_cons_op(&mut self, f: Term, x: Term, list: Term) -> CheckResult<Term> {
        let Some((tail, nil)) = self.list_parts(f, list)? else {
            return Ok(self.stuck());
        };
        let mut elems = Vec::with_capacity(tail.len() + 1);
        elems.push(x);
        append_terms(&mut elems, &tail);
        self.list_build(f, &elems, nil)
    }
    /// The elements of two lists of `f` that end in the same nil, with
    /// that nil; `None` if one is not a list or the ends differ.
    #[allow(clippy::type_complexity)]
    fn list_pair(
        &mut self,
        f: Term,
        x: Term,
        y: Term,
    ) -> CheckResult<Option<(Vec<Term>, Vec<Term>, Term)>> {
        let Some((xs, nil)) = self.list_parts(f, x)? else {
            return Ok(None);
        };
        let Some((ys, other_nil)) = self.list_parts(f, y)? else {
            return Ok(None);
        };
        if other_nil != nil {
            return Ok(None);
        }
        Ok(Some((xs, ys, nil)))
    }
    fn list_concat(&mut self, f: Term, x: Term, y: Term) -> CheckResult<Term> {
        let Some((xs, ys, nil)) = self.list_pair(f, x, y)? else {
            return Ok(self.stuck());
        };
        let left = self.is_left_assoc(f)?;
        let mut both = Vec::with_capacity(xs.len() + ys.len());
        if left {
            append_terms(&mut both, &ys);
            append_terms(&mut both, &xs);
        } else {
            append_terms(&mut both, &xs);
            append_terms(&mut both, &ys);
        }
        self.list_build(f, &both, nil)
    }
    /// `list_minclude` and `list_meq`: whether the second list is included
    /// in the first as a multiset, or equal to it.
    fn list_inclusion(&mut self, op: EvalOp, f: Term, x: Term, y: Term) -> CheckResult<Term> {
        let Some((xs, ys, _)) = self.list_pair(f, x, y)? else {
            return Ok(self.stuck());
        };
        let (foreign, contained) = multiset_inclusion(&xs, &ys);
        let equality = match op {
            EvalOp::ListMeq => true,
            _ => false,
        };
        if !equality {
            return self.boolean(contained);
        }
        if foreign {
            return self.boolean(false);
        }
        if !contained {
            return self.boolean(false);
        }
        let ys = match self.list_parts(f, y)? {
            Some((ys, _)) => ys,
            None => return Err(CheckError::InvalidConstructor),
        };
        self.boolean(xs.len() == ys.len())
    }
    /// `list_inter` and `list_diff`.
    fn list_selection(&mut self, op: EvalOp, f: Term, x: Term, y: Term) -> CheckResult<Term> {
        let Some((xs, ys, nil)) = self.list_pair(f, x, y)? else {
            return Ok(self.stuck());
        };
        let paired = match op {
            EvalOp::ListInter => true,
            _ => false,
        };
        let kept = multiset_select(&xs, &ys, paired);
        self.list_build(f, &kept, nil)
    }
    /// The list operators on one list, `a[1]`.
    fn list_of_one(&mut self, op: EvalOp, f: Term, a: &[Term]) -> CheckResult<Term> {
        let Some((xs, nil)) = self.list_parts(f, a[1])? else {
            return match op {
                EvalOp::ListSingletonIntro => {
                    let nil = self.list_nil_for(f, a[1])?;
                    self.list_build(f, &[a[1]], nil)
                }
                _ => Ok(self.stuck()),
            };
        };
        match op {
            EvalOp::ListLength => self.numeral(Integer::from(xs.len())),
            EvalOp::ListNth => self.list_nth(&xs, a[2]),
            EvalOp::ListFind => self.numeral(match position(&xs, a[2]) {
                Some(i) => Integer::from(i),
                None => Integer::one().neg(),
            }),
            EvalOp::ListRev => self.list_build(f, &reversed(&xs), nil),
            EvalOp::ListSingletonElim => Ok(if xs.len() == 1 { xs[0] } else { a[1] }),
            EvalOp::ListSingletonIntro => Ok(a[1]),
            EvalOp::ListErase => self.list_build(f, &without_first(&xs, a[2]), nil),
            EvalOp::ListEraseAll => self.list_build(f, &without(&xs, a[2]), nil),
            EvalOp::ListSetof => self.list_build(f, &first_occurrences(&xs), nil),
            _ => Ok(self.stuck()),
        }
    }
    fn list_nth(&mut self, xs: &[Term], index: Term) -> CheckResult<Term> {
        Ok(match self.object_index(index)? {
            Some(n) => {
                if (n as usize) < xs.len() {
                    xs[n as usize]
                } else {
                    self.stuck()
                }
            }
            None => self.stuck(),
        })
    }
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
match s.cached_program(ProgramId(58), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24mk_5ftrans(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(58), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn case_3_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_0_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_1_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match cases_0_0_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_cmd_step_proven"
pub fn eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fpush_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fis_5fbool_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5fpush_5fproven_5fcheck(s, v0, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fpush_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fpush_5fproven(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_push_proven"
pub fn eo__24eo_5fpush_5fproven(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fpush_5fproven(s, a0, a1);
s.leave();
result
}
pub(super) fn case_3_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmd_2estep, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fcmd_5fstep_5fproven(s, a0, v1, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fpush_5fproven(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_0_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24eo_5fpf, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24eo_5fprog_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fscope(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_scope"
pub fn eo__24eo_5fprog_5fscope(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fscope(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2escope, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fal_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a2 != v1 { return Ok(None); }
let v2 = match s.destruct(Constructor::eo__24emb_5findl_2econs, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v2 else { return Ok(None); }
;
let v3 = fields[0];
let v4 = fields[1];
let v5 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v5 { return Ok(None); }
let v6 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24eo_5fpf, &[v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fprog_5fscope(s, a3, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_cmd_step_pop_proven"
pub fn eo__24eo_5fcmd_5fstep_5fpop_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fso_2eassume_5fpush, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fcmd_5fstep_5fpop_5fproven(s, a0, a2, a3, v4, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fpush_5fproven(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v6)))
}
pub(super) fn case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([a0, v2, a2, a3, a4])))
}
pub(super) fn case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Next<[Term; 5]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2eStuck, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Next<[Term; 5]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4) {
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
// EO program "$eo_invoke_cmd_step_pop"
pub fn eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmd_2estep_5fpop, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5finvoke_5fcmd_5fstep_5fpop(s, a0, a0, v1, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn cases_0_1_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match cases_0_0_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24eo_5finvoke_5fcmd(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_invoke_cmd"
pub fn eo__24eo_5finvoke_5fcmd(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fcmd(s, a0, a1);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fcmdl_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5finvoke_5fcmd(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v3, v2])))
}
pub(super) fn step_eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$eo_invoke_cmd_list"
pub fn eo__24eo_5finvoke_5fcmd_5flist(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5finvoke_5fcmd_5flist(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fso_2eassume_5fpush, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_1_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fs_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([v2])))
}
pub(super) fn case_2_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_3_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24eo_5fstate_5fis_5fclosed(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5fstate_5fis_5fclosed(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
// EO program "$eo_state_is_closed"
pub fn eo__24eo_5fstate_5fis_5fclosed(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fstate_5fis_5fclosed(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fstate_5fis_5frefutation(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5finvoke_5fcmd_5fcheck_5fproven(s, a0, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5fstate_5fis_5fclosed(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24eo_5fstate_5fis_5frefutation(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fstate_5fis_5frefutation(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_state_is_refutation"
pub fn eo__24eo_5fstate_5fis_5frefutation(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fstate_5fis_5frefutation(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fchecker_5fis_5frefutation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fs_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24eo_5finvoke_5fassume_5flist(s, v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24eo_5finvoke_5fcmd_5flist(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24eo_5fstate_5fis_5frefutation(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24eo_5fchecker_5fis_5frefutation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fchecker_5fis_5frefutation(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_checker_is_refutation"
pub fn eo__24eo_5fchecker_5fis_5frefutation(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fchecker_5fis_5frefutation(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_pattern_nat_zero(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v5)))
}
pub(super) fn case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([a0, a1, a2, v2, v4, a5])))
}
// EO program "$eo_datatype_cons_selectors_rec"
pub fn eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3, a4, a5];
match s.cached_program(ProgramId(4), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(4), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term, mut a4: Term, mut a5: Term) -> CheckResult<Term> {
loop {
match step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) {
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
pub(super) fn step_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Next<[Term; 6]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Next<[Term; 6]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fDtSel, &[a0, a1, a2, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5fedt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.native_op(NativeOp::NatSucc, &[a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, a0, a1, a2, v10, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v14)))
}
pub(super) fn case_1_eo__24eo_5fdatatype_5fconstructors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_datatype_constructors_rec"
pub fn eo__24eo_5fdatatype_5fconstructors_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(5), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fdatatype_5fconstructors_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(5), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
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
pub(super) fn case_0_eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fdd_5fresolve(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fdatatype_5fcons_5fselectors_5frec(s, v1, v2, v3, v4, v3, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fdt_5fselectors_5fmain(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
Ok(s.stuck())
}
// EO program "$eo_dt_selectors_main"
pub fn eo__24eo_5fdt_5fselectors_5fmain(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdt_5fselectors_5fmain(s, a0);
s.leave();
result
}
pub(super) fn case_1_eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5fdt_5fselectors_5fmain(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fdt_5fselectors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fdt_5fselectors(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_dt_selectors"
pub fn eo__24eo_5fdt_5fselectors(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fdt_5fselectors(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBoolean, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eBoolean, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eNumeral, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fRational, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eRational, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_3_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fString, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5fsm_2eString, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn cases_0_0_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_4_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fBinary, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fsm_2eBinary, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.raw(Lit::Str(EoString::from_code_points(vec![64,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.native_op(NativeOp::StringPrefixEq, &[v0, a0]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_to_smt_reserved_datatype_name"
pub fn eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fedd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn if_1_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eTypeRef, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDatatypeTypeRef, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_1_eo__24eo_5fto_5fsmt_5ftype(s, v2, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fguard(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
Some(false) => {
Ok(a1)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fguard(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.native_op(NativeOp::Teq, &[a0, v0]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24smtx_5ftypeof_5fguard(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fguard(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fguard(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_guard"
pub fn eo__24smtx_5ftypeof_5fguard(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fguard(s, a0, a1);
s.leave();
result
}
pub(super) fn case_4_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUSort, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eUSort, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_6_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_7_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Real, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn if_2_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, condition: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.native_op(NativeOp::IntToNat, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_8_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_BitVec, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24emb_5fNumeral, v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zleq, &[v6, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_2_eo__24eo_5fto_5fsmt_5ftype(s, v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_9_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_11_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_to_smt_datatype"
pub fn eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(42), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(42), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdatatype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdatatype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdatatype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5fdatatype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$eo_to_smt_datatype_cons"
pub fn eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(43), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(43), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5fdatatype_5fcons(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$eo_to_smt_datatype_decl"
pub fn eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(44), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(44), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fedd_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fto_5fsmt_5fdatatype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fdd_2econs, &[v1, v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
// EO program "$eo_to_smt_type"
pub fn eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(46), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt_5ftype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(46), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match cases_0_0_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDatatypeType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24eo_5fto_5fsmt_5ftype(s, v3, v2, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_3_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eDtcAppType, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fguard(s, v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof_5fguard(s, v3, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_5_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.is_node(v4, Some(Constructor::eo__24emb_5fFunType)) { Ok(v) => v, Err(e) => return Err(e) };
if !v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fto_5fsmt_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eFunType, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof_5fguard(s, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24smtx_5ftypeof_5fguard(s, v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_10_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fguard(s, v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn cases_0_0_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5fto_5fsmt_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt_5ftype(s: &mut Store, condition: Term, v2: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
Some(false) => {
let v5 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_5_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fString, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eVar, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v2: Term, v1: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fsm_2eDtCons, &[v1, v6, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_6_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match if_0_eo__24eo_5fto_5fsmt(s, v4, v2, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn if_1_eo__24eo_5fto_5fsmt(s: &mut Store, condition: Term, v2: Term, v1: Term, v3: Term, v4: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
Some(false) => {
let v7 = match eo__24eo_5fto_5fsmt_5fdatatype_5fdecl(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__24emb_5fsm_2eDtSel, &[v1, v7, v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_7_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fDtSel, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = fields[3];
let v5 = match eo__24eo_5fto_5fsmt_5freserved_5fdatatype_5fname(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_1_eo__24eo_5fto_5fsmt(s, v5, v2, v1, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_1_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_8_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fUConst, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::UconstId, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eUConst, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_14_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$eo_to_smt"
pub fn eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(41), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24eo_5fto_5fsmt(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(41), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match cases_0_0_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_3_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_9_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2enot, &[v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_10_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2eand, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_11_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d_3e, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_12_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24eo_5fto_5fsmt(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5fsm_2e_3d, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_13_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match eo__24eo_5fto_5fsmt(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24eo_5fto_5fsmt(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fsm_2eApply, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_2_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_3_eo__24eo_5fto_5fsmt(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24eo_5fto_5fsmt(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_1_eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dd_has_dt"
pub fn eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(59), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdd_5fhas_5fdt(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(59), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdd_5fhas_5fdt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdd_5fhas_5fdt(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdd_5fhas_5fdt(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5fdd_5fhas_5fdt(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::Or, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_1_eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dd_lookup"
pub fn eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(60), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdd_5flookup(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(60), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdd_5flookup(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24smtx_5fdd_5flookup(s, v4, v2, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_0_eo__24smtx_5fdd_5flookup(s: &mut Store, condition: Term, v2: Term, a0: Term, v3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v5 = match eo__24smtx_5fdd_5flookup(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_1_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
Ok(Some(Next::Again([v2])))
}
pub(super) fn case_3_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
pub(super) fn case_4_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn case_5_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn cases_0_1_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_4_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_2_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_decl_inhabited"
pub fn eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(61), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdecl_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(61), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdecl_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdecl_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdecl_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.native_op(NativeOp::Streq, &[a0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_0_eo__24smtx_5fdecl_5finhabited(s, v4, v2, v3, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn if_0_eo__24smtx_5fdecl_5finhabited(s: &mut Store, condition: Term, v2: Term, v3: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match eo__24smtx_5fdt_5finhabited(s, v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match eo__24smtx_5fdecl_5finhabited(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
// EO program "$smtx_dt_cons_inhabited"
pub fn eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(63), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(63), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fdt_5fcons_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24smtx_5fdecl_5finhabited(s, v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdt_5fcons_5finhabited(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fcons_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5fcons_5finhabited(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$smtx_dt_inhabited"
pub fn eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(65), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5finhabited(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(65), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5finhabited(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5finhabited(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdt_5fcons_5finhabited(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5finhabited(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Or, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$smtx_inhabited_type"
pub fn eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(69), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5finhabited_5ftype(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(69), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5finhabited_5ftype(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5finhabited_5ftype(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match cases_0_0_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_2_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdecl_5finhabited(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v3)))
}
pub(super) fn cases_0_0_eo__24smtx_5finhabited_5ftype(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if let Some(found) = match case_0_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_6_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_7_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eFunType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_8_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_bool(false) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_9_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_2_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdd_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_decl_wf_rec"
pub fn eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(62), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdecl_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(62), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdecl_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdecl_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdecl_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdd_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5fdt_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5finhabited_5ftype(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5fdecl_5fwf_5frec(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5fdd_5fhas_5fdt(s, v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::Not, &[v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_op(NativeOp::And, &[v7, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.native_op(NativeOp::And, &[v6, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.native_op(NativeOp::And, &[v4, v11]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
// EO program "$smtx_dt_cons_wf_rec"
pub fn eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(64), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(64), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match eo__24smtx_5fdd_5fhas_5fdt(s, v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fcons_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::And, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
// EO program "$smtx_dt_wf_rec"
pub fn eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(67), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fwf_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(67), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fwf_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fwf_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdt_5fcons_5fwf_5frec(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5fwf_5frec(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
// EO program "$smtx_type_wf_rec"
pub fn eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(74), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftype_5fwf_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(74), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match cases_0_0_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eMap, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5finhabited_5ftype(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftype_5fwf_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::And, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.native_op(NativeOp::And, &[v5, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_3_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSet, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::And, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_4_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eSeq, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5finhabited_5ftype(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24smtx_5ftype_5fwf_5frec(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::And, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_5_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDatatype, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdd_5fhas_5fdt(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdecl_5fwf_5frec(s, v2, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_0_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24smtx_5ftype_5fwf_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_2_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dtc_resolve"
pub fn eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(68), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdtc_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(68), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fdtc_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5ftsm_2eTypeRef, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[v5, v6]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_1_eo__24smtx_5fdtc_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdtc_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5fdtc_2econs, &[v1, v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn case_1_eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo__24emb_5fdt_2enull, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$smtx_dt_resolve"
pub fn eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(66), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fdt_5fresolve(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(66), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fdt_5fresolve(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24smtx_5fdt_5fresolve(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5fdtc_5fresolve(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5fdt_5fresolve(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
Ok(Some(Next::Done(v4)))
}
pub(super) fn case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v7 else { return Ok(None); }
;
let v8 = fields[0];
let v9 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v9, v10, v8])))
}
pub(super) fn case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([v2, v4, a2])))
}
pub(super) fn case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2) {
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
// EO program "$smtx_ret_typeof_sel_rec"
pub fn eo__24smtx_5fret_5ftypeof_5fsel_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(71), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(71), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24smtx_5fret_5ftypeof_5fsel(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5fdd_5flookup(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24smtx_5fdt_5fresolve(s, v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match eo__24smtx_5fret_5ftypeof_5fsel_5frec(s, v1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24smtx_5fret_5ftypeof_5fsel(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5fret_5ftypeof_5fsel(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_ret_typeof_sel"
pub fn eo__24smtx_5fret_5ftypeof_5fsel(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5fret_5ftypeof_5fsel(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eRegLan, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_bool(true) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_0_eo__24smtx_5ftype_5fwf_5fcomponent(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5finhabited_5ftype(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24smtx_5ftype_5fwf_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.native_op(NativeOp::And, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24smtx_5ftype_5fwf_5fcomponent(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftype_5fwf_5fcomponent(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_type_wf_component"
pub fn eo__24smtx_5ftype_5fwf_5fcomponent(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftype_5fwf_5fcomponent(s, a0);
s.leave();
result
}
pub(super) fn case_2_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5ftype_5fwf_5fcomponent(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$smtx_type_wf"
pub fn eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(72), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftype_5fwf(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(72), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24smtx_5ftype_5fwf(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eFunType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftype_5fwf_5fcomponent(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftype_5fwf(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::And, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_0_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eBoolean, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_1_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eNumeral, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eInt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_2_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eRational, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eReal, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn if_0_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eChar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eSeq, &[v3]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
Some(false) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_3_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eString, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match s.native_op(NativeOp::StringValid, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match if_0_eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_0_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_1_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.native_op(NativeOp::IntToNat, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eBitVec, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_4_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eBinary, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.raw(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Zleq, &[v3, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::IntPow2, &[v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.native_op(NativeOp::ModTotal, &[v2, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.native_op(NativeOp::Zeq, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::And, &[v4, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match if_1_eo__24smtx_5ftypeof(s, v8, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn if_2_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24smtx_5ftypeof(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5f_3d(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.native_op(NativeOp::Teq, &[a0, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24smtx_5ftypeof_5f_3d(s, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof_5fguard(s, a0, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24smtx_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5f_3d(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_="
pub fn eo__24smtx_5ftypeof_5f_3d(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5f_3d(s, a0, a1);
s.leave();
result
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fite(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a1)
}
Some(false) => {
let v2 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.native_op(NativeOp::Teq, &[a1, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24smtx_5ftypeof_5fite(s, v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fite(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_ite"
pub fn eo__24smtx_5ftypeof_5fite(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fite(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.construct(Constructor::eo__24emb_5fdtc_2eunit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
Ok(Some(Next::Done(a0)))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_pattern_succ(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
Ok(Some(Next::Again([a0, v2, v4])))
}
pub(super) fn case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
// EO program "$smtx_typeof_dt_cons_rec"
pub fn eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(78), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(78), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) {
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
pub(super) fn step_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fdt_2esum, a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fdtc_2econs, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = match s.native_pattern_nat_zero(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v6 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo__24emb_5fdt_2esum, &[v5, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_nat_zero() { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, a0, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__24emb_5ftsm_2eDtcAppType, &[v4, v9]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, condition: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a1)
}
Some(false) => {
let v1 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24smtx_5ftype_5fwf(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match if_0_eo__24smtx_5ftypeof_5fguard_5fwf(s, v0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fguard_5fwf(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_guard_wf"
pub fn eo__24smtx_5ftypeof_5fguard_5fwf(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fguard_5fwf(s, a0, a1);
s.leave();
result
}
pub(super) fn case_11_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtCons, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5fdd_5flookup(s, v1, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5fdt_5fresolve(s, v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, v5, v7, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v4, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn if_0_eo__24smtx_5ftypeof_5fapply(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eFunType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::Teq, &[v1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_0_eo__24smtx_5ftypeof_5fapply(s, v3, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fguard(s, v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn if_1_eo__24smtx_5ftypeof_5fapply(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(v2)
}
Some(false) => {
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v4)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5ftsm_2eDtcAppType, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.native_op(NativeOp::Teq, &[v1, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match if_1_eo__24smtx_5ftypeof_5fapply(s, v3, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof_5fguard(s, v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_2_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
if let Some(found) = match case_0_eo__24smtx_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24smtx_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24smtx_5ftypeof_5fapply(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$smtx_typeof_apply"
pub fn eo__24smtx_5ftypeof_5fapply(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24smtx_5ftypeof_5fapply(s, a0, a1);
s.leave();
result
}
pub(super) fn case_15_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eVar, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_16_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eUConst, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v3))
}
pub(super) fn case_17_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn cases_0_4_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_16_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_17_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_1_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_4_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$smtx_typeof"
pub fn eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_type(TypeCacheKind::Smt, cache_args[0]) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24smtx_5ftypeof(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_type(TypeCacheKind::Smt, cache_args[0], value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Term> {
if let Some(found) = match cases_1_0_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_1_1_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_5_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2enot, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.native_op(NativeOp::Teq, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_2_eo__24smtx_5ftypeof(s, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_6_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eand, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_4_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_7_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eor, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_6_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_8_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3d_3e, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.native_op(NativeOp::Teq, &[v3, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_8_eo__24smtx_5ftypeof(s, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_9_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2e_3d, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5f_3d(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn case_10_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eite, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = fields[2];
let v4 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24smtx_5ftypeof(s, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24smtx_5ftypeof_5fite(s, v4, v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn case_12_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eApply, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtSel, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = fields[3];
let v8 = match eo__24smtx_5fret_5ftypeof_5fsel(s, v4, v5, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24smtx_5fret_5ftypeof_5fsel(s, v4, v5, v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eFunType, &[v9, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24smtx_5ftypeof_5fapply(s, v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24smtx_5ftypeof_5fguard_5fwf(s, v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_13_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eApply, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match s.destruct(Constructor::eo__24emb_5fsm_2eDtTester, v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v3 else { return Ok(None); }
;
let v4 = fields[0];
let v5 = fields[1];
let v6 = fields[2];
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24smtx_5fdd_5flookup(s, v4, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24smtx_5fdt_5fresolve(s, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24smtx_5ftypeof_5fdt_5fcons_5frec(s, v7, v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__24emb_5ftsm_2eDatatype, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__24emb_5ftsm_2eFunType, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24smtx_5ftypeof_5fapply(s, v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24smtx_5ftypeof_5fguard(s, v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_14_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.destruct(Constructor::eo__24emb_5fsm_2eApply, a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v0 else { return Ok(None); }
;
let v1 = fields[0];
let v2 = fields[1];
let v3 = match eo__24smtx_5ftypeof(s, v1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match eo__24smtx_5ftypeof_5fapply(s, v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn cases_0_1_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_3_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_0_eo__24smtx_5ftypeof(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_0_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_1_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_2_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_3_eo__24smtx_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_4_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_3_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_5_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_8_eo__24smtx_5ftypeof(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, true) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v6 = match eo__24smtx_5ftypeof(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__24emb_5ftsm_2eBool, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.native_op(NativeOp::Teq, &[v6, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_7_eo__24smtx_5ftypeof(s, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo__24emb_5ftsm_2eNone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
// The entry points of checking, to be called on the checker's stack (see
// front.rs): they call generated functions, and nothing generated calls
// them, so the generator puts them after all the generated functions.
impl Store {
    /// Check the entire proof state machine, including typing, assumptions,
    /// step-pop, premise lookup and the final closed refutation test. To be
    /// called on the checker's stack: see `Store::check_refutation`.
    pub(crate) fn check_refutation_inner(&mut self, assumptions: Term, commands: Term) -> CheckResult<bool> {
        self.calls = 0;
        let answer = generated::eo__24eo_5fchecker_5fis_5frefutation(self, assumptions, commands)?;
        self.is_native_true(answer)
    }
    /// The verdict on a proof. To be called on the checker's stack: see
    /// `Store::check_proof`.
    pub(crate) fn check_proof_inner(&mut self, assumptions: Term, commands: Term) -> CheckResult<Verdict> {
        if !self.check_refutation_inner(assumptions, commands)? {
            return Ok(Verdict::Incorrect);
        }
        if !true {
            return Ok(Verdict::Incomplete);
        }
        if !self.arguments_translate(assumptions, None)? {
            return Ok(Verdict::Incomplete);
        }
        let mut list = commands;
        loop {
            if self.is_node(list, Some(Constructor::eo__24emb_5fcmdl_2enil))? {
                return Ok(Verdict::Correct);
            }
            let Some(cs) = self.node_fields(list, Some(Constructor::eo__24emb_5fcmdl_2econs))? else {
                return Ok(Verdict::Incorrect);
            };
            let c = cs[0];
            if let Some(fs) = self.node_fields(c, Some(Constructor::eo__24emb_5fcmd_2eassume_5fpush))? {
                if !self.has_translation(fs[0])? {
                    return Ok(Verdict::Incomplete);
                }
            } else if let Some(fs) = self.node_fields(c, Some(Constructor::eo__24emb_5fcmd_2estep))? {
                let rule = match self.view(fs[0])? {
                    TermData::Node(rule, _) => *rule,
                    _ => return Ok(Verdict::Incorrect),
                };
                if !self.arguments_translate(fs[1], Some(rule))? {
                    return Ok(Verdict::Incomplete);
                }
            }
            list = cs[1];
        }
    }

    /// The number of arguments of a rule whose arguments have a mask.
    #[allow(clippy::match_single_binding)]
    fn mask_len(rule: Constructor) -> Option<usize> {
        match rule {
            
            _ => None,
        }
    }
    /// What the mask of `rule` asks of its `i`-th argument.
    #[allow(clippy::match_single_binding)]
    fn mask_kind(rule: Constructor, i: usize) -> Option<ArgKind> {
        match rule {
            
            _ => None,
        }
    }

    fn translation_type(&mut self, t: Term) -> CheckResult<Term> {
        let t = generated::eo__24eo_5fto_5fsmt(self, t)?; generated::eo__24smtx_5ftypeof(self, t)
    }
    fn translation_sort(&mut self, t: Term) -> CheckResult<Term> {
        generated::eo__24eo_5fto_5fsmt_5ftype(self, t)
    }
    fn translation_type_wf(&mut self, t: Term, component: bool) -> CheckResult<bool> {
        let b = if component { generated::eo__24smtx_5ftype_5fwf_5fcomponent(self, t)? } else { generated::eo__24smtx_5ftype_5fwf(self, t)? }; self.is_native_true(b)
    }
    fn has_translation(&mut self, t: Term) -> CheckResult<bool> {
        let ty = self.translation_type(t)?;
        Ok(!self.is_stuck(ty)? && !self.is_node(ty, Some(Constructor::eo__24emb_5ftsm_2eNone))?)
    }
    fn argument_translates(&mut self, t: Term, which: ArgKind) -> CheckResult<bool> {
        match which {
            ArgKind::Term => self.has_translation(t),
            ArgKind::Type => {
                let ty = self.translation_sort(t)?;
                self.translation_type_wf(ty, false)
            }
            ArgKind::WfTerm => {
                if !self.has_translation(t)? {
                    return Ok(false);
                }
                let ty = self.translation_type(t)?;
                self.translation_type_wf(ty, false)
            }
            ArgKind::WfElem => {
                let ty = self.translation_type(t)?;
                self.translation_type_wf(ty, true)
            }
            ArgKind::List => {
                let mut list = t;
                loop {
                    if self.is_node(list, Some(Constructor::eo__24eo_5fList_5fnil))? {
                        return Ok(true);
                    }
                    let Some((fx, tail)) = self.unapply(list)? else {
                        return Ok(false);
                    };
                    let Some((f, x)) = self.unapply(fx)? else {
                        return Ok(false);
                    };
                    if !self.is_node(f, Some(Constructor::eo__24eo_5fList_5fcons))? || !self.has_translation(x)? {
                        return Ok(false);
                    }
                    list = tail;
                }
            }
            ArgKind::Unknown => Err(CheckError::InvalidConstructor),
        }
    }
    /// Whether the arguments translate: each as a term, or, for a rule
    /// with a mask, as its mask says.
    fn arguments_translate(
        &mut self,
        mut args: Term,
        rule: Option<Constructor>,
    ) -> CheckResult<bool> {
        let mask = match rule {
            Some(rule) => match Self::mask_len(rule) {
                Some(len) => Some((rule, len)),
                None => None,
            },
            None => None,
        };
        let mut i = 0;
        loop {
            if self.is_node(args, Some(Constructor::eo__24emb_5fal_2enil))? {
                return Ok(match mask {
                    Some((_, len)) => i == len,
                    None => true,
                });
            }
            let Some(fs) = self.node_fields(args, Some(Constructor::eo__24emb_5fal_2econs))? else {
                return Ok(false);
            };
            let which = match mask {
                Some((rule, _)) => match Self::mask_kind(rule, i) {
                    Some(k) => k,
                    None => return Ok(false),
                },
                None => ArgKind::Term,
            };
            if !self.argument_translates(fs[0], which)? {
                return Ok(false);
            }
            args = fs[1];
            i += 1;
        }
    }
}
