//! Generated functions, module 8 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
pub(super) fn more_13_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v229: Term, v230: Term, a5: Term, a6: Term, v227: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a3: Term, a2: Term, a4: Term, a7: Term) -> CheckResult<Option<Term>> {
let v231 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v229 != v231 { return Ok(None); }
let v232 = match s.unapply(v230) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v233, v234)) = v232 else { return Ok(None); }
;
let v235 = match s.unapply(v233) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v236, v237)) = v235 else { return Ok(None); }
;
let v238 = match s.unapply(v236) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v239, v240)) = v238 else { return Ok(None); }
;
let v241 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v239 != v241 { return Ok(None); }
let v242 = match s.unapply(v240) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v243, v244)) = v242 else { return Ok(None); }
;
let v245 = match s.unapply(v243) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v246, v247)) = v245 else { return Ok(None); }
;
let v248 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v246 != v248 { return Ok(None); }
if v247 != a5 { return Ok(None); }
more_14_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v244, v237, a6, v234, a5, v227, v126, a1, v119, a15, a8, a0, a3, a2, a4, a7)
}
pub(super) fn more_12_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v207: Term, a2: Term, v175: Term, a5: Term, a6: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a3: Term, a4: Term, a7: Term) -> CheckResult<Option<Term>> {
let v213 = match s.unapply(v207) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v214, v215)) = v213 else { return Ok(None); }
;
let v216 = match s.unapply(v214) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v217, v218)) = v216 else { return Ok(None); }
;
let v219 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v217 != v219 { return Ok(None); }
let v220 = match s.unapply(v218) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v221, v222)) = v220 else { return Ok(None); }
;
let v223 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v221 != v223 { return Ok(None); }
if v222 != a2 { return Ok(None); }
let v224 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v215 != v224 { return Ok(None); }
let v225 = match s.unapply(v175) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v226, v227)) = v225 else { return Ok(None); }
;
let v228 = match s.unapply(v226) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v229, v230)) = v228 else { return Ok(None); }
;
more_13_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v229, v230, a5, a6, v227, v126, a1, v119, a15, a8, a0, a3, a2, a4, a7)
}
pub(super) fn more_11_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v185: Term, a3: Term, v182: Term, a2: Term, v175: Term, a5: Term, a6: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a4: Term, a7: Term) -> CheckResult<Option<Term>> {
if v185 != a3 { return Ok(None); }
let v198 = match s.unapply(v182) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v199, v200)) = v198 else { return Ok(None); }
;
let v201 = match s.unapply(v199) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v202, v203)) = v201 else { return Ok(None); }
;
let v204 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v202 != v204 { return Ok(None); }
if v203 != a3 { return Ok(None); }
let v205 = match s.unapply(v200) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v206, v207)) = v205 else { return Ok(None); }
;
let v208 = match s.unapply(v206) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v209, v210)) = v208 else { return Ok(None); }
;
let v211 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v209 != v211 { return Ok(None); }
let v212 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v210 != v212 { return Ok(None); }
more_12_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v207, a2, v175, a5, a6, v126, a1, v119, a15, a8, a0, a3, a4, a7)
}
pub(super) fn more_10_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v178: Term, a2: Term, a3: Term, v175: Term, a5: Term, a6: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a4: Term, a7: Term) -> CheckResult<Option<Term>> {
let v180 = match s.unapply(v178) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v181, v182)) = v180 else { return Ok(None); }
;
let v183 = match s.unapply(v181) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v184, v185)) = v183 else { return Ok(None); }
;
let v186 = match s.unapply(v184) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v187, v188)) = v186 else { return Ok(None); }
;
let v189 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v187 != v189 { return Ok(None); }
let v190 = match s.unapply(v188) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v191, v192)) = v190 else { return Ok(None); }
;
let v193 = match s.unapply(v191) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v194, v195)) = v193 else { return Ok(None); }
;
let v196 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v194 != v196 { return Ok(None); }
if v195 != a2 { return Ok(None); }
let v197 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v192 != v197 { return Ok(None); }
more_11_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v185, a3, v182, a2, v175, a5, a6, v126, a1, v119, a15, a8, a0, a4, a7)
}
pub(super) fn more_9_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v165: Term, a4: Term, v162: Term, v148: Term, v133: Term, a2: Term, a3: Term, a5: Term, a6: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v167 = match s.unapply(v165) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v168, v169)) = v167 else { return Ok(None); }
;
let v170 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v168 != v170 { return Ok(None); }
if v169 != a4 { return Ok(None); }
let v171 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v162 != v171 { return Ok(None); }
let v172 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v148 != v172 { return Ok(None); }
let v173 = match s.unapply(v133) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v174, v175)) = v173 else { return Ok(None); }
;
let v176 = match s.unapply(v174) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v177, v178)) = v176 else { return Ok(None); }
;
let v179 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v177 != v179 { return Ok(None); }
more_10_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v178, a2, a3, v175, a5, a6, v126, a1, v119, a15, a8, a0, a4, a7)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v147: Term, a3: Term, a4: Term, v148: Term, v133: Term, a2: Term, a5: Term, a6: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v149 = match s.unapply(v147) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v150, v151)) = v149 else { return Ok(None); }
;
let v152 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v150 != v152 { return Ok(None); }
let v153 = match s.unapply(v151) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v154, v155)) = v153 else { return Ok(None); }
;
let v156 = match s.unapply(v154) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v157, v158)) = v156 else { return Ok(None); }
;
let v159 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v157 != v159 { return Ok(None); }
if v158 != a3 { return Ok(None); }
let v160 = match s.unapply(v155) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v161, v162)) = v160 else { return Ok(None); }
;
let v163 = match s.unapply(v161) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v164, v165)) = v163 else { return Ok(None); }
;
let v166 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v164 != v166 { return Ok(None); }
more_9_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v165, a4, v162, v148, v133, a2, a3, a5, a6, v126, a1, v119, a15, a8, a0, a7)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v128: Term, v130: Term, v129: Term, a3: Term, a4: Term, a2: Term, a5: Term, a6: Term, v126: Term, a1: Term, v119: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
if v128 != v130 { return Ok(None); }
let v131 = match s.unapply(v129) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v132, v133)) = v131 else { return Ok(None); }
;
let v134 = match s.unapply(v132) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v135, v136)) = v134 else { return Ok(None); }
;
let v137 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v135 != v137 { return Ok(None); }
let v138 = match s.unapply(v136) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v139, v140)) = v138 else { return Ok(None); }
;
let v141 = match s.unapply(v139) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v142, v143)) = v141 else { return Ok(None); }
;
let v144 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v142 != v144 { return Ok(None); }
let v145 = match s.literal(Lit::Numeral(Integer::from(2u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v143 != v145 { return Ok(None); }
let v146 = match s.unapply(v140) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v147, v148)) = v146 else { return Ok(None); }
;
more_8_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v147, a3, a4, v148, v133, a2, a5, a6, v126, a1, v119, a15, a8, a0, a7)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v111: Term, v113: Term, v112: Term, a6: Term, v98: Term, a14: Term, a3: Term, a4: Term, a2: Term, a5: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
if v111 != v113 { return Ok(None); }
if v112 != a6 { return Ok(None); }
let v114 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v98 != v114 { return Ok(None); }
let v115 = match s.destruct(Constructor::eo__24eo_5fpf, a14) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v115 else { return Ok(None); }
;
let v116 = fields[0];
let v117 = match s.unapply(v116) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v118, v119)) = v117 else { return Ok(None); }
;
let v120 = match s.unapply(v118) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v121, v122)) = v120 else { return Ok(None); }
;
let v123 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v121 != v123 { return Ok(None); }
let v124 = match s.unapply(v122) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v125, v126)) = v124 else { return Ok(None); }
;
let v127 = match s.unapply(v125) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v128, v129)) = v127 else { return Ok(None); }
;
let v130 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v128, v130, v129, a3, a4, a2, a5, a6, v126, a1, v119, a15, a8, a0, a7)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, a13: Term, a5: Term, a6: Term, a14: Term, a3: Term, a4: Term, a2: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v94 = match s.destruct(Constructor::eo__24eo_5fpf, a13) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v94 else { return Ok(None); }
;
let v95 = fields[0];
let v96 = match s.unapply(v95) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v97, v98)) = v96 else { return Ok(None); }
;
let v99 = match s.unapply(v97) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v100, v101)) = v99 else { return Ok(None); }
;
let v102 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v100 != v102 { return Ok(None); }
let v103 = match s.unapply(v101) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v104, v105)) = v103 else { return Ok(None); }
;
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v107 != v109 { return Ok(None); }
if v108 != a5 { return Ok(None); }
let v110 = match s.unapply(v105) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v111, v113, v112, a6, v98, a14, a3, a4, a2, a5, a1, a15, a8, a0, a7)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v79: Term, a5: Term, v80: Term, a13: Term, a6: Term, a14: Term, a3: Term, a4: Term, a2: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v81 = match s.unapply(v79) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v82, v83)) = v81 else { return Ok(None); }
;
let v84 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v82 != v84 { return Ok(None); }
let v85 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v89 != v91 { return Ok(None); }
if v90 != a5 { return Ok(None); }
let v92 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v87 != v92 { return Ok(None); }
let v93 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v80 != v93 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, a13, a5, a6, a14, a3, a4, a2, a1, a15, a8, a0, a7)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v65: Term, a2: Term, v66: Term, a3: Term, v59: Term, a12: Term, a5: Term, a13: Term, a6: Term, a14: Term, a4: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v67 = match s.unapply(v65) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
let v70 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v68 != v70 { return Ok(None); }
if v69 != a2 { return Ok(None); }
let v71 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v72, v73)) = v71 else { return Ok(None); }
;
let v74 = match s.construct(Constructor::eo_int_2epow2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v72 != v74 { return Ok(None); }
if v73 != a3 { return Ok(None); }
let v75 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v59 != v75 { return Ok(None); }
let v76 = match s.destruct(Constructor::eo__24eo_5fpf, a12) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v76 else { return Ok(None); }
;
let v77 = fields[0];
let v78 = match s.unapply(v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v79, v80)) = v78 else { return Ok(None); }
;
more_4_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v79, a5, v80, a13, a6, a14, a3, a4, a2, a1, a15, a8, a0, a7)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v50: Term, v52: Term, v51: Term, a2: Term, v48: Term, v41: Term, a11: Term, a3: Term, a12: Term, a5: Term, a13: Term, a6: Term, a14: Term, a4: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
if v50 != v52 { return Ok(None); }
if v51 != a2 { return Ok(None); }
let v53 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v48 != v53 { return Ok(None); }
let v54 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v41 != v54 { return Ok(None); }
let v55 = match s.destruct(Constructor::eo__24eo_5fpf, a11) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v55 else { return Ok(None); }
;
let v56 = fields[0];
let v57 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v61, v62)) = v60 else { return Ok(None); }
;
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v61 != v63 { return Ok(None); }
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v65, a2, v66, a3, v59, a12, a5, a13, a6, a14, a4, a1, a15, a8, a0, a7)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v11: Term, v4: Term, a10: Term, a2: Term, a11: Term, a3: Term, a12: Term, a5: Term, a13: Term, a6: Term, a14: Term, a4: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
let v35 = match s.literal(Lit::Numeral(Integer::from(64u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v35 { return Ok(None); }
let v36 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v36 { return Ok(None); }
let v37 = match s.destruct(Constructor::eo__24eo_5fpf, a10) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v37 else { return Ok(None); }
;
let v38 = fields[0];
let v39 = match s.unapply(v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v40, v41)) = v39 else { return Ok(None); }
;
let v42 = match s.unapply(v40) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v43 != v45 { return Ok(None); }
let v46 = match s.unapply(v44) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v50, v52, v51, a2, v48, v41, a11, a3, a12, a5, a13, a6, a14, a4, a1, a15, a8, a0, a7)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s: &mut Store, v20: Term, v22: Term, v21: Term, a3: Term, v18: Term, a4: Term, v11: Term, v4: Term, a10: Term, a2: Term, a11: Term, a12: Term, a5: Term, a13: Term, a6: Term, a14: Term, a1: Term, a15: Term, a8: Term, a0: Term, a7: Term) -> CheckResult<Option<Term>> {
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
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v34 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v11, v4, a10, a2, a11, a3, a12, a5, a13, a6, a14, a4, a1, a15, a8, a0, a7)
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
more_0_eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v20, v22, v21, a3, v18, a4, v11, v4, a10, a2, a11, a12, a5, a13, a6, a14, a1, a15, a8, a0, a7)
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
pub(super) fn more_79_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v52: Term, v54: Term, v56: Term, v58: Term, v60: Term, v62: Term, v64: Term) -> CheckResult<Option<Term>> {
let v65 = match eo__24eo_5fprog_5fbv_2dextract_2dmult_2dleading_2dbit(s, v2, v5, v8, v11, v14, v17, v20, v23, v26, v52, v54, v56, v58, v60, v62, v64) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v65))
}
pub(super) fn more_78_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v33: Term, v36: Term, v39: Term, v42: Term, v45: Term, v48: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term, v52: Term) -> CheckResult<Option<Term>> {
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
more_79_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v11, v14, v17, v20, v23, v26, v52, v54, v56, v58, v60, v62, v64)
}
pub(super) fn more_77_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v27: Term, v28: Term, a3: Term, a0: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term, v23: Term, v26: Term) -> CheckResult<Option<Term>> {
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
more_78_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v33, v36, v39, v42, v45, v48, v2, v5, v8, v11, v14, v17, v20, v23, v26, v52)
}
pub(super) fn case_367_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_77_eo__24eo_5fcmd_5fstep_5fproven(s, v27, v28, a3, a0, v2, v5, v8, v11, v14, v17, v20, v23, v26)
}
pub(super) fn cases_0_91_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_364_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_365_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_366_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_367_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_22_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_88_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_89_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_90_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_91_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, a4: Term, a3: Term, a0: Term, v73: Term, v68: Term) -> CheckResult<Option<Term>> {
let v74 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_extract, &[a4, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v74, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v77, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v73, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v68, v80) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v81))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, a0: Term, a2: Term, a1: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v62 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v62, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v70, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v69, v72) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, a4, a3, a0, v73, v68)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, v46: Term, a4: Term, a2: Term, a0: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
let v47 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.unapply(v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v51, v52)) = v50 else { return Ok(None); }
;
let v53 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v51 != v53 { return Ok(None); }
if v52 != a4 { return Ok(None); }
let v54 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.unapply(v55) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v58 != v60 { return Ok(None); }
if v59 != a2 { return Ok(None); }
let v61 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v56 != v61 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, a0, a2, a1, a3, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, v18: Term, v31: Term, a7: Term, a3: Term, a1: Term, a8: Term, a4: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
if v18 != v31 { return Ok(None); }
let v32 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a3 { return Ok(None); }
let v41 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a1 { return Ok(None); }
let v45 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v45 else { return Ok(None); }
;
let v46 = fields[0];
more_2_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, v46, a4, a2, a0, a1, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s: &mut Store, v15: Term, a1: Term, a7: Term, a3: Term, a8: Term, a4: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
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
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v30 { return Ok(None); }
let v31 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, v18, v31, a7, a3, a1, a8, a4, a2, a0)
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
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fbv_2dudiv_2dpow2_2dnot_2done(s, v15, a1, a7, a3, a8, a4, a2, a0)
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
pub(super) fn more_80_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_368_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_80_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero(s: &mut Store, v8: Term, v11: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v7, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvudiv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v9, v10) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dudiv_2dzero(s, v8, v11, v7)
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
pub(super) fn case_369_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
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
pub(super) fn case_370_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v85: Term, v88: Term, v84: Term, v79: Term) -> CheckResult<Option<Term>> {
let v89 = match s.apply(v85, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.literal(Lit::Binary(BitVec::new(0, &Integer::from(0u32)))) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v89, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v84, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v79, v92) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v93))
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v76: Term, a1: Term, v75: Term, v73: Term, a3: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v76, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v73, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v81, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v80, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_concat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.construct(Constructor::eo_extract, &[a4, v86]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v87, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v85, v88, v84, v79)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v65: Term, v66: Term, a1: Term, v63: Term, a0: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v67 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v65 != v67 { return Ok(None); }
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
if v70 != a1 { return Ok(None); }
let v72 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v63 != v72 { return Ok(None); }
let v73 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v76, a1, v75, v73, a3, a4, a0)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v43: Term, a1: Term, a8: Term, a4: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v48 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.construct(Constructor::eo_int_2elog2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
if v50 != a1 { return Ok(None); }
let v52 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v52 else { return Ok(None); }
;
let v53 = fields[0];
let v54 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.unapply(v55) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v58 != v60 { return Ok(None); }
if v59 != a4 { return Ok(None); }
let v61 = match s.unapply(v56) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v65, v66, a1, v63, a0, a2, a3, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v18: Term, v31: Term, a7: Term, a3: Term, a2: Term, a1: Term, a8: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
if v18 != v31 { return Ok(None); }
let v32 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
let v34 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a3 { return Ok(None); }
let v41 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v47 { return Ok(None); }
if v46 != a2 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v43, a1, a8, a4, a0, a2, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s: &mut Store, v15: Term, a1: Term, a7: Term, a3: Term, a2: Term, a8: Term, a4: Term, a0: Term) -> CheckResult<Option<Term>> {
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
let v30 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v30 { return Ok(None); }
let v31 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v18, v31, a7, a3, a2, a1, a8, a4, a0)
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
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v14 else { return Ok(None); }
;
let v15 = fields[0];
more_0_eo__24eo_5fprog_5fbv_2durem_2dpow2_2dnot_2done(s, v15, a1, a7, a3, a2, a8, a4, a0)
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
pub(super) fn more_81_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_371_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_81_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn cases_0_92_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_368_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_369_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_370_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_371_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2durem_2done(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvurem, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
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
pub(super) fn case_372_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2durem_2dself(s: &mut Store, v14: Term, a0: Term, v13: Term, a1: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
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
more_0_eo__24eo_5fprog_5fbv_2durem_2dself(s, v14, a0, v13, a1)
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
pub(super) fn case_373_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
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
pub(super) fn case_374_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
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
pub(super) fn case_375_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn cases_0_93_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_372_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_373_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_374_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_375_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dashr_2dzero(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_bvashr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
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
pub(super) fn case_376_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dugt_2durem(s: &mut Store, v28: Term, v38: Term, v20: Term) -> CheckResult<Option<Term>> {
let v39 = match s.apply(v28, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v20, v39) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v40))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dugt_2durem(s: &mut Store, v23: Term, v26: Term, v21: Term, a0: Term, a2: Term, v20: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v23, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v21, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_bvugt, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v31, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v36, v37) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dugt_2durem(s, v28, v38, v20)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dugt_2durem(s: &mut Store, a0: Term, a1: Term, v14: Term, v13: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v25 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dugt_2durem(s, v23, v26, v21, a0, a2, v20)
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
more_0_eo__24eo_5fprog_5fbv_2dugt_2durem(s, a0, a1, v14, v13, a2)
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
pub(super) fn more_82_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fbv_2dugt_2durem(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_377_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_82_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dult_2done(s: &mut Store, v22: Term, v28: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v22, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v32, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v31, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v29, v35) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v36))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dult_2done(s: &mut Store, v18: Term, a0: Term, v11: Term, v4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dult_2done(s, v22, v28, a0, a1)
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
more_0_eo__24eo_5fprog_5fbv_2dult_2done(s, v18, a0, v11, v4, a1)
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
pub(super) fn case_378_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s: &mut Store, a3: Term, a0: Term, v29: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo_sign_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v32))
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s: &mut Store, v17: Term, a2: Term, v18: Term, a1: Term, a0: Term, a3: Term) -> CheckResult<Option<Term>> {
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a2 { return Ok(None); }
let v23 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v23 { return Ok(None); }
let v24 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_sign_5fextend, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v24, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s, a3, a0, v29)
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
more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s, v17, a2, v18, a1, a0, a3)
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
pub(super) fn more_83_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d1(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_379_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_83_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_94_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_376_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_377_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_378_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_379_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s: &mut Store, v43: Term, v45: Term, v42: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v42, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_zero_5fextend, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v50))
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s: &mut Store, v32: Term, a1: Term, v29: Term, a2: Term, a0: Term, a3: Term) -> CheckResult<Option<Term>> {
if v32 != a1 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a2 { return Ok(None); }
let v41 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v36 != v41 { return Ok(None); }
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_zero_5fextend, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, v43, v45, v42, a3, a0)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s: &mut Store, v4: Term, a5: Term, a3: Term, a1: Term, a2: Term, a0: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v18 else { return Ok(None); }
;
let v19 = fields[0];
let v20 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a3 { return Ok(None); }
let v27 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, v32, a1, v29, a2, a0, a3)
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
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, v4, a5, a3, a1, a2, a0)
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
pub(super) fn more_84_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fbv_2dmerge_2dsign_2dextend_2d2(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_380_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_84_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, v105: Term, v110: Term, v103: Term, v102: Term, v71: Term) -> CheckResult<Option<Term>> {
let v111 = match s.apply(v105, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v103, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v102, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v71, v115) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v116))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, v98: Term, v84: Term, v72: Term, a0: Term, a5: Term, a3: Term, a2: Term, v71: Term) -> CheckResult<Option<Term>> {
let v99 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v98, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v84, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v72, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_extract, &[a5, v106]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v105, v110, v103, v102, v71)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a6: Term, a5: Term, a3: Term, a2: Term, v86: Term, a4: Term, v85: Term, v84: Term, v72: Term, a0: Term, v71: Term) -> CheckResult<Option<Term>> {
let v87 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v87, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v86, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v93, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v92, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v91, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v85, v97) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v98, v84, v72, a0, a5, a3, a2, v71)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a6: Term, a5: Term, a3: Term, a2: Term, v74: Term, a4: Term, v73: Term, v72: Term, a0: Term, v71: Term) -> CheckResult<Option<Term>> {
let v75 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v79, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v73, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, a6, a5, a3, a2, v86, a4, v85, v84, v72, a0, v71)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, a1: Term, a0: Term, a3: Term, a2: Term, a6: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v63, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, a6, a5, a3, a2, v74, a4, v73, v72, a0, v71)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, v47: Term, a6: Term, a3: Term, a1: Term, a0: Term, a2: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v60 != a3 { return Ok(None); }
let v62 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v62 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, a1, a0, a3, a2, a6, a5, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, v32: Term, a5: Term, v29: Term, a0: Term, a9: Term, a6: Term, a3: Term, a1: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
if v32 != a5 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a0 { return Ok(None); }
let v45 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v36 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v47, a6, a3, a1, a0, a2, a5, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s: &mut Store, v17: Term, v18: Term, a8: Term, a5: Term, a0: Term, a9: Term, a6: Term, a3: Term, a1: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
let v24 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v24 { return Ok(None); }
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
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v32, a5, v29, a0, a9, a6, a3, a1, a2, a4)
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
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d1(s, v17, v18, a8, a5, a0, a9, a6, a3, a1, a2, a4)
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
pub(super) fn more_85_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_381_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_85_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, v105: Term, v110: Term, v103: Term, v102: Term, v71: Term) -> CheckResult<Option<Term>> {
let v111 = match s.apply(v105, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v103, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v102, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v71, v115) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v116))
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, v98: Term, v84: Term, v72: Term, a0: Term, a5: Term, a3: Term, a2: Term, v71: Term) -> CheckResult<Option<Term>> {
let v99 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v98, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v84, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v72, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_extract, &[a5, v106]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v107, v109) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v105, v110, v103, v102, v71)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a6: Term, a5: Term, a3: Term, a2: Term, v86: Term, a4: Term, v85: Term, v84: Term, v72: Term, a0: Term, v71: Term) -> CheckResult<Option<Term>> {
let v87 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v87, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v86, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v93, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v92, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v91, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v85, v97) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v98, v84, v72, a0, a5, a3, a2, v71)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a6: Term, a5: Term, a3: Term, a2: Term, v74: Term, a4: Term, v73: Term, v72: Term, a0: Term, v71: Term) -> CheckResult<Option<Term>> {
let v75 = match s.construct(Constructor::eo_extract, &[a6, a5]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v75, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v74, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v79, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v73, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, a6, a5, a3, a2, v86, a4, v85, v84, v72, a0, v71)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, a3: Term, a2: Term, a1: Term, a0: Term, a6: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v67, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v63, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, a6, a5, a3, a2, v74, a4, v73, v72, a0, v71)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, v47: Term, a6: Term, a3: Term, a2: Term, a1: Term, a0: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v60 != a3 { return Ok(None); }
let v62 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v57 != v62 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, a3, a2, a1, a0, a6, a5, a4)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, v32: Term, a5: Term, v29: Term, a0: Term, a9: Term, a6: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
if v32 != a5 { return Ok(None); }
let v34 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a0 { return Ok(None); }
let v45 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v36 != v45 { return Ok(None); }
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v47, a6, a3, a2, a1, a0, a5, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s: &mut Store, v17: Term, v18: Term, a8: Term, a5: Term, a0: Term, a9: Term, a6: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
let v24 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v24 { return Ok(None); }
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
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v32, a5, v29, a0, a9, a6, a3, a2, a1, a4)
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
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2deq_2dconst_2d2(s, v17, v18, a8, a5, a0, a9, a6, a3, a2, a1, a4)
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
pub(super) fn more_86_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v20: Term) -> CheckResult<Option<Term>> {
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
pub(super) fn case_382_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_86_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v24, v2, v5, v8, v11, v14, v17, v20)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, v68: Term, v58: Term, v46: Term) -> CheckResult<Option<Term>> {
let v69 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v68, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v58, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v46, v71) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v72))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, v53: Term, v56: Term, v47: Term, a0: Term, a4: Term, a3: Term, a2: Term, v46: Term) -> CheckResult<Option<Term>> {
let v57 = match s.apply(v53, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v47, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_extract, &[a4, v62]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v63, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v61, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v59, v67) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v68, v58, v46)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, v42: Term, v44: Term, v38: Term, a5: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v45 = match s.apply(v42, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v38, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_extract, &[a5, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v48, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v54, v55) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v53, v56, v47, a0, a4, a3, a2, v46)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, v34: Term, v35: Term, a3: Term, v32: Term, a1: Term, a0: Term, a2: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a3 { return Ok(None); }
let v37 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v37 { return Ok(None); }
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v42, v44, v38, a5, a4, a3, a2, a1, a0)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a7: Term, a5: Term, a3: Term, a1: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
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
if v28 != a5 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v34, v35, a3, v32, a1, a0, a2, a5, a4)
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
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v17, v19, v18, a0, v11, a7, a5, a3, a1, a2, a4)
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
pub(super) fn more_87_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d1(s, v2, v5, v8, v11, v14, v17, v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn case_383_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_87_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v21, v24, v2, v5, v8, v11, v14, v17)
}
pub(super) fn cases_0_95_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_380_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_381_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_382_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_383_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_23_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_92_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_93_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_94_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_95_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_2_5_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_1_20_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_21_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_22_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_1_23_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, v68: Term, v58: Term, v46: Term) -> CheckResult<Option<Term>> {
let v69 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v68, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v58, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v46, v71) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v72))
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, v53: Term, v56: Term, v47: Term, a0: Term, a4: Term, a3: Term, a2: Term, v46: Term) -> CheckResult<Option<Term>> {
let v57 = match s.apply(v53, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v47, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_extract, &[a4, v62]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v63, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v61, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v59, v67) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v68, v58, v46)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, v42: Term, v44: Term, v38: Term, a5: Term, a4: Term, a3: Term, a2: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
let v45 = match s.apply(v42, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v38, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_extract, &[a5, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v49, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v48, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v54, v55) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v53, v56, v47, a0, a4, a3, a2, v46)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, v34: Term, v35: Term, a3: Term, v32: Term, a2: Term, a1: Term, a0: Term, a5: Term, a4: Term) -> CheckResult<Option<Term>> {
let v36 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v34 != v36 { return Ok(None); }
if v35 != a3 { return Ok(None); }
let v37 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v37 { return Ok(None); }
let v38 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v42, v44, v38, a5, a4, a3, a2, a1, a0)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a7: Term, a5: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
if v17 != v19 { return Ok(None); }
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
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
if v28 != a5 { return Ok(None); }
let v30 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v34, v35)) = v33 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v34, v35, a3, v32, a2, a1, a0, a5, a4)
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
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v17, v19, v18, a0, v11, a7, a5, a3, a2, a1, a4)
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
pub(super) fn more_88_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2deq_2dconst_2d2(s, v2, v5, v8, v11, v14, v17, v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn case_384_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_88_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v21, v24, v2, v5, v8, v11, v14, v17)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, a4: Term, a3: Term, a2: Term, v62: Term, v60: Term) -> CheckResult<Option<Term>> {
let v63 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_extract, &[a4, v63]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v64, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v62, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v60, v68) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v69))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, v49: Term, a2: Term, a1: Term, a0: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
if v49 != a2 { return Ok(None); }
let v52 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v53, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v52, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v61, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, a4, a3, a2, v62, v60)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, v32: Term, a2: Term, v25: Term, a1: Term, a4: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
if v32 != a2 { return Ok(None); }
let v35 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.destruct(Constructor::eo_zero_5fextend, v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
if v39 != a1 { return Ok(None); }
let v40 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.destruct(Constructor::eo_extract, v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v43 else { return Ok(None); }
;
let v44 = fields[0];
let v45 = fields[1];
if v44 != a4 { return Ok(None); }
let v46 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v46 { return Ok(None); }
let v47 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.destruct(Constructor::eo_int_5fto_5fbv, v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v50 else { return Ok(None); }
;
let v51 = fields[0];
if v51 != a3 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, v49, a2, a1, a0, a3, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a6: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.destruct(Constructor::eo_int_5fto_5fbv, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v33 else { return Ok(None); }
;
let v34 = fields[0];
if v34 != a3 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, v32, a2, v25, a1, a4, a3, a0)
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
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, v17, v19, v18, a0, v11, a6, a3, a2, a1, a4)
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
pub(super) fn more_89_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d1(s, v2, v5, v8, v11, v14, v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_385_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_89_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v18, v21, v2, v5, v8, v11, v14)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, a4: Term, v62: Term, a3: Term, a2: Term, v61: Term, a0: Term, v60: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo_extract, &[a4, v62]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v64, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v63, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v61, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v60, v68) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v69))
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, v49: Term, a2: Term, a3: Term, a1: Term, a0: Term, a4: Term) -> CheckResult<Option<Term>> {
if v49 != a2 { return Ok(None); }
let v52 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v53, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_zero_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v52, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, a4, v62, a3, a2, v61, a0, v60)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, v32: Term, a2: Term, v25: Term, a1: Term, a4: Term, a3: Term, a0: Term) -> CheckResult<Option<Term>> {
if v32 != a2 { return Ok(None); }
let v35 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.destruct(Constructor::eo_zero_5fextend, v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
if v39 != a1 { return Ok(None); }
let v40 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v41, v42)) = v40 else { return Ok(None); }
;
let v43 = match s.destruct(Constructor::eo_extract, v41) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v43 else { return Ok(None); }
;
let v44 = fields[0];
let v45 = fields[1];
if v44 != a4 { return Ok(None); }
let v46 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v46 { return Ok(None); }
let v47 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v48, v49)) = v47 else { return Ok(None); }
;
let v50 = match s.destruct(Constructor::eo_int_5fto_5fbv, v48) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v50 else { return Ok(None); }
;
let v51 = fields[0];
if v51 != a3 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, v49, a2, a3, a1, a0, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s: &mut Store, v17: Term, v19: Term, v18: Term, a0: Term, v11: Term, a6: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.destruct(Constructor::eo_int_5fto_5fbv, v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v33 else { return Ok(None); }
;
let v34 = fields[0];
if v34 != a3 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, v32, a2, v25, a1, a4, a3, a0)
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
more_0_eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, v17, v19, v18, a0, v11, a6, a3, a2, a1, a4)
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
pub(super) fn more_90_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fprog_5fbv_2dzero_2dextend_2dult_2dconst_2d2(s, v2, v5, v8, v11, v14, v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_386_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_90_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v18, v21, v2, v5, v8, v11, v14)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, a4: Term, v145: Term, a3: Term, a2: Term, v144: Term, v142: Term) -> CheckResult<Option<Term>> {
let v146 = match s.construct(Constructor::eo_extract, &[a4, v145]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v147, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v146, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v144, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v142, v150) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v151))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, a1: Term, a0: Term, a3: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v134 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v136, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v135, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v139, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v138, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v134, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v143, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, a4, v145, a3, a2, v144, v142)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v119: Term, v121: Term, v120: Term, a4: Term, v117: Term, a0: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v119 != v121 { return Ok(None); }
if v120 != a4 { return Ok(None); }
let v122 = match s.unapply(v117) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v123, v124)) = v122 else { return Ok(None); }
;
let v125 = match s.unapply(v123) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v126, v127)) = v125 else { return Ok(None); }
;
let v128 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v126 != v128 { return Ok(None); }
let v129 = match s.unapply(v127) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v130, v131)) = v129 else { return Ok(None); }
;
let v132 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v130 != v132 { return Ok(None); }
if v131 != a0 { return Ok(None); }
let v133 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v124 != v133 { return Ok(None); }
more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, a1, a0, a3, a2, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v107: Term, v109: Term, v108: Term, a0: Term, v101: Term, v60: Term, v4: Term, a6: Term, a4: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v107 != v109 { return Ok(None); }
if v108 != a0 { return Ok(None); }
let v110 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v101 != v110 { return Ok(None); }
let v111 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v111 { return Ok(None); }
let v112 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v112 { return Ok(None); }
let v113 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v113 else { return Ok(None); }
;
let v114 = fields[0];
let v115 = match s.unapply(v114) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v116, v117)) = v115 else { return Ok(None); }
;
let v118 = match s.unapply(v116) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v119, v120)) = v118 else { return Ok(None); }
;
let v121 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v119, v121, v120, a4, v117, a0, a1, a3, a2)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v92: Term, a3: Term, v90: Term, v79: Term, a0: Term, v60: Term, v4: Term, a6: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v92 != a3 { return Ok(None); }
let v93 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v90 != v93 { return Ok(None); }
let v94 = match s.unapply(v79) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v95, v96)) = v94 else { return Ok(None); }
;
let v97 = match s.destruct(Constructor::eo_int_5fto_5fbv, v95) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v97 else { return Ok(None); }
;
let v98 = fields[0];
if v98 != a3 { return Ok(None); }
let v99 = match s.unapply(v96) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v100, v101)) = v99 else { return Ok(None); }
;
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v103 != v105 { return Ok(None); }
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v107, v109, v108, a0, v101, v60, v4, a6, a4, a1, a3, a2)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v73: Term, a3: Term, v74: Term, a2: Term, v67: Term, a0: Term, v60: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v75 = match s.destruct(Constructor::eo_int_5fto_5fbv, v73) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v75 else { return Ok(None); }
;
let v76 = fields[0];
if v76 != a3 { return Ok(None); }
if v74 != a2 { return Ok(None); }
let v77 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v78, v79)) = v77 else { return Ok(None); }
;
let v80 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v81 != v83 { return Ok(None); }
let v84 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v85, v86)) = v84 else { return Ok(None); }
;
let v87 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v85 != v87 { return Ok(None); }
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.destruct(Constructor::eo_int_5fto_5fbv, v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v91 else { return Ok(None); }
;
let v92 = fields[0];
more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v92, a3, v90, v79, a0, v60, v4, a6, a4, a1, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v55: Term, a0: Term, v48: Term, v11: Term, a3: Term, a2: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v55 != a0 { return Ok(None); }
let v57 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v48 != v57 { return Ok(None); }
let v58 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo_bvuge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
let v72 = match s.unapply(v70) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v73, a3, v74, a2, v67, a0, v60, v4, a6, a4, a1)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v37: Term, v30: Term, a3: Term, a0: Term, v11: Term, a2: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v40 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v40 { return Ok(None); }
let v41 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.destruct(Constructor::eo_int_5fto_5fbv, v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v44 else { return Ok(None); }
;
let v45 = fields[0];
if v45 != a3 { return Ok(None); }
let v46 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v52 { return Ok(None); }
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v55, a0, v48, v11, a3, a2, v4, a6, a4, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, v20: Term, v22: Term, v21: Term, a3: Term, a2: Term, v18: Term, a0: Term, v11: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.destruct(Constructor::eo_int_5fto_5fbv, v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
if v27 != a3 { return Ok(None); }
if v25 != a2 { return Ok(None); }
let v28 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v34 { return Ok(None); }
let v35 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.destruct(Constructor::eo_int_5fto_5fbv, v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
if v39 != a3 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v37, v30, a3, a0, v11, a2, v4, a6, a4, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v20, v22, v21, a3, a2, v18, a0, v11, v4, a6, a4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sign-extend-ult-const-1"
pub fn eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn more_91_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d1(s, v2, v5, v8, v11, v14, v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_387_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_91_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v18, v21, v2, v5, v8, v11, v14)
}
pub(super) fn cases_0_96_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_384_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_385_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_386_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_387_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v143: Term, v141: Term, v137: Term) -> CheckResult<Option<Term>> {
let v144 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v143, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v141, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v137, v146) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v147))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v131: Term, a0: Term, v130: Term, a3: Term, a2: Term, v129: Term, a4: Term) -> CheckResult<Option<Term>> {
let v132 = match s.apply(v131, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v130, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v134, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v133, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v129, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_extract, &[a4, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v139, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v138, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v142]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v143, v141, v137)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v118: Term, a0: Term, v119: Term, a1: Term, a3: Term, a2: Term, a4: Term) -> CheckResult<Option<Term>> {
let v120 = match s.unapply(v118) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v121, v122)) = v120 else { return Ok(None); }
;
let v123 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v121 != v123 { return Ok(None); }
let v124 = match s.unapply(v122) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v125, v126)) = v124 else { return Ok(None); }
;
let v127 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v125 != v127 { return Ok(None); }
if v126 != a0 { return Ok(None); }
let v128 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v119 != v128 { return Ok(None); }
let v129 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v131, a0, v130, a3, a2, v129, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v104: Term, a0: Term, v97: Term, v56: Term, a7: Term, a4: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Option<Term>> {
if v104 != a0 { return Ok(None); }
let v106 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v97 != v106 { return Ok(None); }
let v107 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v56 != v107 { return Ok(None); }
let v108 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v108 else { return Ok(None); }
;
let v109 = fields[0];
let v110 = match s.unapply(v109) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.unapply(v111) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v114, v115)) = v113 else { return Ok(None); }
;
let v116 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v114 != v116 { return Ok(None); }
if v115 != a4 { return Ok(None); }
let v117 = match s.unapply(v112) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v118, v119)) = v117 else { return Ok(None); }
;
more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v118, a0, v119, a1, a3, a2, a4)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v86: Term, v75: Term, a3: Term, a0: Term, v56: Term, a7: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v89 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v86 != v89 { return Ok(None); }
let v90 = match s.unapply(v75) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.destruct(Constructor::eo_int_5fto_5fbv, v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v93 else { return Ok(None); }
;
let v94 = fields[0];
if v94 != a3 { return Ok(None); }
let v95 = match s.unapply(v92) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v96, v97)) = v95 else { return Ok(None); }
;
let v98 = match s.unapply(v96) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v99, v100)) = v98 else { return Ok(None); }
;
let v101 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v99 != v101 { return Ok(None); }
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v103 != v105 { return Ok(None); }
more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v104, a0, v97, v56, a7, a4, a1, a3, a2)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v72: Term, a3: Term, v70: Term, a2: Term, v63: Term, a0: Term, v56: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v72 != a3 { return Ok(None); }
if v70 != a2 { return Ok(None); }
let v73 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v77 != v79 { return Ok(None); }
let v80 = match s.unapply(v78) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v81 != v83 { return Ok(None); }
let v84 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v85, v86)) = v84 else { return Ok(None); }
;
let v87 = match s.destruct(Constructor::eo_int_5fto_5fbv, v85) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v87 else { return Ok(None); }
;
let v88 = fields[0];
if v88 != a3 { return Ok(None); }
more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v86, v75, a3, a0, v56, a7, a4, a1, a2)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v4: Term, v51: Term, a6: Term, a3: Term, a2: Term, a0: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v4 != v51 { return Ok(None); }
let v52 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v52 else { return Ok(None); }
;
let v53 = fields[0];
let v54 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.unapply(v55) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v58, v59)) = v57 else { return Ok(None); }
;
let v60 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v58 != v60 { return Ok(None); }
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v65, v66)) = v64 else { return Ok(None); }
;
let v67 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v65 != v67 { return Ok(None); }
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.destruct(Constructor::eo_int_5fto_5fbv, v69) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v71 else { return Ok(None); }
;
let v72 = fields[0];
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v72, a3, v70, a2, v63, a0, v56, a7, a4, a1)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v38: Term, v40: Term, v39: Term, a0: Term, v36: Term, v11: Term, a3: Term, a2: Term, v4: Term, a6: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v38 != v40 { return Ok(None); }
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
if v43 != a0 { return Ok(None); }
let v45 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v36 != v45 { return Ok(None); }
let v46 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.destruct(Constructor::eo_int_5fto_5fbv, v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v49 else { return Ok(None); }
;
let v50 = fields[0];
if v50 != a3 { return Ok(None); }
if v48 != a2 { return Ok(None); }
let v51 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v4, v51, a6, a3, a2, a0, a7, a4, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, v20: Term, v22: Term, v21: Term, a3: Term, v18: Term, a0: Term, v11: Term, a2: Term, v4: Term, a6: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.destruct(Constructor::eo_int_5fto_5fbv, v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
if v27 != a3 { return Ok(None); }
let v28 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v28 { return Ok(None); }
let v29 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.destruct(Constructor::eo_int_5fto_5fbv, v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v32 else { return Ok(None); }
;
let v33 = fields[0];
if v33 != a3 { return Ok(None); }
let v34 = match s.unapply(v31) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v38, v40, v39, a0, v36, v11, a3, a2, v4, a6, a7, a4, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v20, v22, v21, a3, v18, a0, v11, a2, v4, a6, a7, a4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sign-extend-ult-const-2"
pub fn eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn more_92_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24eo_5fpf, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d2(s, v2, v5, v8, v11, v14, v28, v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_388_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_92_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, a3: Term, a2: Term, v145: Term, v143: Term, a0: Term, v142: Term) -> CheckResult<Option<Term>> {
let v146 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v146, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v145, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v143, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v149, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v142, v150) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v151))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, a3: Term, a2: Term, a1: Term, a0: Term, a4: Term) -> CheckResult<Option<Term>> {
let v134 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v136, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v135, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v139, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v138, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v134, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_extract, &[a4, v144]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, a3, a2, v145, v143, a0, v142)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, v119: Term, v121: Term, v120: Term, a4: Term, v117: Term, a0: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v119 != v121 { return Ok(None); }
if v120 != a4 { return Ok(None); }
let v122 = match s.unapply(v117) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v123, v124)) = v122 else { return Ok(None); }
;
let v125 = match s.unapply(v123) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v126, v127)) = v125 else { return Ok(None); }
;
let v128 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v126 != v128 { return Ok(None); }
let v129 = match s.unapply(v127) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v130, v131)) = v129 else { return Ok(None); }
;
let v132 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v130 != v132 { return Ok(None); }
if v131 != a0 { return Ok(None); }
let v133 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v124 != v133 { return Ok(None); }
more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, a3, a2, a1, a0, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, v107: Term, v109: Term, v108: Term, a0: Term, v101: Term, v60: Term, v4: Term, a6: Term, a4: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v107 != v109 { return Ok(None); }
if v108 != a0 { return Ok(None); }
let v110 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v101 != v110 { return Ok(None); }
let v111 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v111 { return Ok(None); }
let v112 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v112 { return Ok(None); }
let v113 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v113 else { return Ok(None); }
;
let v114 = fields[0];
let v115 = match s.unapply(v114) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v116, v117)) = v115 else { return Ok(None); }
;
let v118 = match s.unapply(v116) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v119, v120)) = v118 else { return Ok(None); }
;
let v121 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v119, v121, v120, a4, v117, a0, a3, a2, a1)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, v92: Term, a3: Term, v90: Term, v83: Term, a0: Term, v60: Term, v4: Term, a6: Term, a4: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v92 != a3 { return Ok(None); }
let v93 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v90 != v93 { return Ok(None); }
let v94 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v95, v96)) = v94 else { return Ok(None); }
;
let v97 = match s.destruct(Constructor::eo_int_5fto_5fbv, v95) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v97 else { return Ok(None); }
;
let v98 = fields[0];
if v98 != a3 { return Ok(None); }
let v99 = match s.unapply(v96) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v100, v101)) = v99 else { return Ok(None); }
;
let v102 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v103, v104)) = v102 else { return Ok(None); }
;
let v105 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v103 != v105 { return Ok(None); }
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v107, v109, v108, a0, v101, v60, v4, a6, a4, a3, a2, a1)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, v73: Term, a3: Term, v74: Term, a2: Term, v67: Term, a0: Term, v60: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v75 = match s.destruct(Constructor::eo_int_5fto_5fbv, v73) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v75 else { return Ok(None); }
;
let v76 = fields[0];
if v76 != a3 { return Ok(None); }
if v74 != a2 { return Ok(None); }
let v77 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v78, v79)) = v77 else { return Ok(None); }
;
let v80 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v78 != v80 { return Ok(None); }
let v81 = match s.unapply(v79) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v82, v83)) = v81 else { return Ok(None); }
;
let v84 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v85, v86)) = v84 else { return Ok(None); }
;
let v87 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v85 != v87 { return Ok(None); }
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.destruct(Constructor::eo_int_5fto_5fbv, v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v91 else { return Ok(None); }
;
let v92 = fields[0];
more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v92, a3, v90, v83, a0, v60, v4, a6, a4, a2, a1)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, v55: Term, a0: Term, v48: Term, v11: Term, a3: Term, a2: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v55 != a0 { return Ok(None); }
let v57 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v48 != v57 { return Ok(None); }
let v58 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v59, v60)) = v58 else { return Ok(None); }
;
let v61 = match s.unapply(v59) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v62, v63)) = v61 else { return Ok(None); }
;
let v64 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v62 != v64 { return Ok(None); }
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.unapply(v66) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v69, v70)) = v68 else { return Ok(None); }
;
let v71 = match s.construct(Constructor::eo_bvuge, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v69 != v71 { return Ok(None); }
let v72 = match s.unapply(v70) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v73, a3, v74, a2, v67, a0, v60, v4, a6, a4, a1)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, v37: Term, v30: Term, a3: Term, a0: Term, v11: Term, a2: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v40 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v40 { return Ok(None); }
let v41 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.destruct(Constructor::eo_int_5fto_5fbv, v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v44 else { return Ok(None); }
;
let v45 = fields[0];
if v45 != a3 { return Ok(None); }
let v46 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v47, v48)) = v46 else { return Ok(None); }
;
let v49 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v52 { return Ok(None); }
let v53 = match s.unapply(v51) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v55, a0, v48, v11, a3, a2, v4, a6, a4, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, v20: Term, v22: Term, v21: Term, a3: Term, a2: Term, v18: Term, a0: Term, v11: Term, v4: Term, a6: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v20 != v22 { return Ok(None); }
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.destruct(Constructor::eo_int_5fto_5fbv, v24) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v26 else { return Ok(None); }
;
let v27 = fields[0];
if v27 != a3 { return Ok(None); }
if v25 != a2 { return Ok(None); }
let v28 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v29, v30)) = v28 else { return Ok(None); }
;
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v32 != v34 { return Ok(None); }
let v35 = match s.unapply(v33) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v36, v37)) = v35 else { return Ok(None); }
;
let v38 = match s.destruct(Constructor::eo_int_5fto_5fbv, v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v38 else { return Ok(None); }
;
let v39 = fields[0];
if v39 != a3 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v37, v30, a3, a0, v11, a2, v4, a6, a4, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v20, v22, v21, a3, a2, v18, a0, v11, v4, a6, a4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sign-extend-ult-const-3"
pub fn eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn more_93_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d3(s, v2, v5, v8, v11, v14, v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn case_389_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f3, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_93_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v18, v21, v2, v5, v8, v11, v14)
}
pub(super) fn more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, a4: Term, a0: Term, v145: Term) -> CheckResult<Option<Term>> {
let v146 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_extract, &[a4, a4]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v147, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v146, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_int_5fto_5fbv, &[v150]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v151, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v149, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v145, v154) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v155))
}
pub(super) fn more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v134: Term, a0: Term, v127: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
if v134 != a0 { return Ok(None); }
let v136 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v127 != v136 { return Ok(None); }
let v137 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.construct(Constructor::eo_bvult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.construct(Constructor::eo_int_5fto_5fbv, &[a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v139, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v138, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_sign_5fextend, &[a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v142, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v141, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v137, v144) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, a4, a0, v145)
}
pub(super) fn more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v117: Term, a4: Term, a0: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v118 = match s.unapply(v117) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v119, v120)) = v118 else { return Ok(None); }
;
let v121 = match s.unapply(v119) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v122, v123)) = v121 else { return Ok(None); }
;
let v124 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v122 != v124 { return Ok(None); }
if v123 != a4 { return Ok(None); }
let v125 = match s.unapply(v120) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v126, v127)) = v125 else { return Ok(None); }
;
let v128 = match s.unapply(v126) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v129, v130)) = v128 else { return Ok(None); }
;
let v131 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v129 != v131 { return Ok(None); }
let v132 = match s.unapply(v130) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v133, v134)) = v132 else { return Ok(None); }
;
let v135 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v133 != v135 { return Ok(None); }
more_7_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v134, a0, v127, a3, a2, a1, a4)
}
pub(super) fn more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v104: Term, a0: Term, v105: Term, v64: Term, a7: Term, a4: Term, a3: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v106 = match s.unapply(v104) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v107, v108)) = v106 else { return Ok(None); }
;
let v109 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v107 != v109 { return Ok(None); }
let v110 = match s.unapply(v108) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v111, v112)) = v110 else { return Ok(None); }
;
let v113 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v111 != v113 { return Ok(None); }
if v112 != a0 { return Ok(None); }
let v114 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v105 != v114 { return Ok(None); }
let v115 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v64 != v115 { return Ok(None); }
let v116 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v116 else { return Ok(None); }
;
let v117 = fields[0];
more_6_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v117, a4, a0, a3, a2, a1)
}
pub(super) fn more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v86: Term, a3: Term, v87: Term, a0: Term, v64: Term, a7: Term, a4: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v88 = match s.unapply(v86) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v89, v90)) = v88 else { return Ok(None); }
;
let v91 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v89 != v91 { return Ok(None); }
let v92 = match s.unapply(v90) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v93, v94)) = v92 else { return Ok(None); }
;
let v95 = match s.destruct(Constructor::eo_int_5fto_5fbv, v93) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v95 else { return Ok(None); }
;
let v96 = fields[0];
if v96 != a3 { return Ok(None); }
let v97 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v97 { return Ok(None); }
let v98 = match s.unapply(v87) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v99, v100)) = v98 else { return Ok(None); }
;
let v101 = match s.destruct(Constructor::eo_int_5fto_5fbv, v99) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v101 else { return Ok(None); }
;
let v102 = fields[0];
if v102 != a3 { return Ok(None); }
let v103 = match s.unapply(v100) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v104, v105)) = v103 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v104, a0, v105, v64, a7, a4, a3, a2, a1)
}
pub(super) fn more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v67: Term, a3: Term, a2: Term, a0: Term, v64: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v69 = match s.unapply(v67) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v70, v71)) = v69 else { return Ok(None); }
;
let v72 = match s.unapply(v70) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v73, v74)) = v72 else { return Ok(None); }
;
let v75 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v73 != v75 { return Ok(None); }
let v76 = match s.unapply(v74) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v77, v78)) = v76 else { return Ok(None); }
;
let v79 = match s.destruct(Constructor::eo_int_5fto_5fbv, v77) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v79 else { return Ok(None); }
;
let v80 = fields[0];
if v80 != a3 { return Ok(None); }
if v78 != a2 { return Ok(None); }
let v81 = match s.unapply(v71) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v82, v83)) = v81 else { return Ok(None); }
;
let v84 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v82 != v84 { return Ok(None); }
let v85 = match s.unapply(v83) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v86, v87)) = v85 else { return Ok(None); }
;
more_4_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v86, a3, v87, a0, v64, a7, a4, a2, a1)
}
pub(super) fn more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v44: Term, v53: Term, v11: Term, a3: Term, a2: Term, v4: Term, a6: Term, a0: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
if v44 != v53 { return Ok(None); }
let v54 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v55, v56)) = v54 else { return Ok(None); }
;
let v57 = match s.destruct(Constructor::eo_int_5fto_5fbv, v55) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v57 else { return Ok(None); }
;
let v58 = fields[0];
if v58 != a3 { return Ok(None); }
if v56 != a2 { return Ok(None); }
let v59 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v59 { return Ok(None); }
let v60 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v60 else { return Ok(None); }
;
let v61 = fields[0];
let v62 = match s.unapply(v61) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v63, v64)) = v62 else { return Ok(None); }
;
let v65 = match s.unapply(v63) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v66, v67)) = v65 else { return Ok(None); }
;
let v68 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v66 != v68 { return Ok(None); }
more_3_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v67, a3, a2, a0, v64, a7, a4, a1)
}
pub(super) fn more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v22: Term, a3: Term, a0: Term, v11: Term, a2: Term, v4: Term, a6: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v37 = match s.unapply(v22) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.destruct(Constructor::eo_int_5fto_5fbv, v38) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v40 else { return Ok(None); }
;
let v41 = fields[0];
if v41 != a3 { return Ok(None); }
let v42 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v43, v44)) = v42 else { return Ok(None); }
;
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
let v49 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v50, v51)) = v49 else { return Ok(None); }
;
let v52 = match s.construct(Constructor::eo__40bvsize, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v50 != v52 { return Ok(None); }
if v51 != a0 { return Ok(None); }
let v53 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v44, v53, v11, a3, a2, v4, a6, a0, a7, a4, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, v18: Term, a3: Term, a0: Term, v11: Term, a2: Term, v4: Term, a6: Term, a7: Term, a4: Term, a1: Term) -> CheckResult<Option<Term>> {
let v20 = match s.unapply(v18) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_bvshl, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v30 { return Ok(None); }
let v31 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v32, v33)) = v31 else { return Ok(None); }
;
let v34 = match s.destruct(Constructor::eo_int_5fto_5fbv, v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v34 else { return Ok(None); }
;
let v35 = fields[0];
if v35 != a3 { return Ok(None); }
let v36 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v36 { return Ok(None); }
more_1_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v22, a3, a0, v11, a2, v4, a6, a7, a4, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_bvule, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_bvnot, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v18, a3, a0, v11, a2, v4, a6, a7, a4, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_bv-sign-extend-ult-const-4"
pub fn eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn more_94_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v18: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24eo_5fpf, &[v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24eo_5fprog_5fbv_2dsign_2dextend_2dult_2dconst_2d4(s, v2, v5, v8, v11, v14, v28, v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_390_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ebv_5fsign_5fextend_5fult_5fconst_5f4, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_94_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v18, v21, v24, v2, v5, v8, v11, v14)
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v19, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v25, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-eq-singleton-emp"
pub fn eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_95_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2deq_2dsingleton_2demp(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_391_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5feq_5fsingleton_5femp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_95_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn cases_0_97_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_388_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_389_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_390_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_391_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dmember_2dsingleton(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v2, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dmember_2dsingleton(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dmember_2dsingleton(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-member-singleton"
pub fn eo__24eo_5fprog_5fsets_2dmember_2dsingleton(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dmember_2dsingleton(s, a0, a1);
s.leave();
result
}
pub(super) fn case_392_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fmember_5fsingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fsets_2dmember_2dsingleton(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dmember_2demp(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dmember_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dmember_2demp(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dmember_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dmember_2demp(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-member-emp"
pub fn eo__24eo_5fprog_5fsets_2dmember_2demp(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dmember_2demp(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_96_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2dmember_2demp(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_393_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fmember_5femp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_96_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dsubset_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2esubset, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dsubset_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dsubset_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-subset-elim"
pub fn eo__24eo_5fprog_5fsets_2dsubset_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dsubset_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_394_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fsubset_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fsets_2dsubset_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dinsert_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2einsert, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v4, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dinsert_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dinsert_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-insert-elim"
pub fn eo__24eo_5fprog_5fsets_2dinsert_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dinsert_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_395_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5finsert_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fsets_2dinsert_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_98_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_392_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_393_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_394_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_395_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dunion_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dunion_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dunion_2dcomm(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-union-comm"
pub fn eo__24eo_5fprog_5fsets_2dunion_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dunion_2dcomm(s, a0, a1);
s.leave();
result
}
pub(super) fn case_396_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5funion_5fcomm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fsets_2dunion_2dcomm(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dinter_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dinter_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dinter_2dcomm(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-inter-comm"
pub fn eo__24eo_5fprog_5fsets_2dinter_2dcomm(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dinter_2dcomm(s, a0, a1);
s.leave();
result
}
pub(super) fn case_397_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5finter_5fcomm, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fsets_2dinter_2dcomm(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dinter_2demp1(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dinter_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dinter_2demp1(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dinter_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dinter_2demp1(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-inter-emp1"
pub fn eo__24eo_5fprog_5fsets_2dinter_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dinter_2demp1(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_97_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2dinter_2demp1(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_398_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5finter_5femp1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_97_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dinter_2demp2(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dinter_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dinter_2demp2(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dinter_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dinter_2demp2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-inter-emp2"
pub fn eo__24eo_5fprog_5fsets_2dinter_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dinter_2demp2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_98_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2dinter_2demp2(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_399_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5finter_5femp2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_98_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn cases_0_99_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_396_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_397_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_398_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_399_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_24_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_96_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_97_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_98_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_99_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dminus_2demp1(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_set_2eminus, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dminus_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dminus_2demp1(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dminus_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dminus_2demp1(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-minus-emp1"
pub fn eo__24eo_5fprog_5fsets_2dminus_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dminus_2demp1(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_99_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2dminus_2demp1(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_400_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fminus_5femp1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_99_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dminus_2demp2(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_set_2eminus, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dminus_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dminus_2demp2(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dminus_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dminus_2demp2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-minus-emp2"
pub fn eo__24eo_5fprog_5fsets_2dminus_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dminus_2demp2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_100_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2dminus_2demp2(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_401_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fminus_5femp2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_100_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dunion_2demp1(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dunion_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dunion_2demp1(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dunion_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dunion_2demp1(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-union-emp1"
pub fn eo__24eo_5fprog_5fsets_2dunion_2demp1(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dunion_2demp1(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_101_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2dunion_2demp1(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_402_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5funion_5femp1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_101_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dunion_2demp2(s: &mut Store, v16: Term, v18: Term, v17: Term, v2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
if v17 != v2 { return Ok(None); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v24))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dunion_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.unapply(v7) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v10, v11)) = v9 else { return Ok(None); }
;
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v10 != v12 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v13 = match s.destruct(Constructor::eo_set_2eempty, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v13 else { return Ok(None); }
;
let v14 = fields[0];
let v15 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dunion_2demp2(s, v16, v18, v17, v2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dunion_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dunion_2demp2(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-union-emp2"
pub fn eo__24eo_5fprog_5fsets_2dunion_2demp2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dunion_2demp2(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_102_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fsets_2dunion_2demp2(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_403_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5funion_5femp2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_102_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn cases_0_100_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_400_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_401_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_402_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_403_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dinter_2dmember(s: &mut Store, v8: Term, v11: Term, a0: Term, a2: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v12, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v7, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dinter_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dinter_2dmember(s, v8, v11, a0, a2, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dinter_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dinter_2dmember(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-inter-member"
pub fn eo__24eo_5fprog_5fsets_2dinter_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dinter_2dmember(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_404_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5finter_5fmember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fsets_2dinter_2dmember(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dminus_2dmember(s: &mut Store, v8: Term, v11: Term, a0: Term, a2: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v13, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v12, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v7, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dminus_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_set_2eminus, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dminus_2dmember(s, v8, v11, a0, a2, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dminus_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dminus_2dmember(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-minus-member"
pub fn eo__24eo_5fprog_5fsets_2dminus_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dminus_2dmember(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_405_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fminus_5fmember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fsets_2dminus_2dmember(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dunion_2dmember(s: &mut Store, v8: Term, v11: Term, a0: Term, a2: Term, v7: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v12, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v7, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dunion_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_set_2emember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dunion_2dmember(s, v8, v11, a0, a2, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dunion_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dunion_2dmember(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-union-member"
pub fn eo__24eo_5fprog_5fsets_2dunion_2dmember(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dunion_2dmember(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_406_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5funion_5fmember, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fsets_2dunion_2dmember(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dchoose_2dsingleton(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2echoose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v0, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dchoose_2dsingleton(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dchoose_2dsingleton(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-choose-singleton"
pub fn eo__24eo_5fprog_5fsets_2dchoose_2dsingleton(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dchoose_2dsingleton(s, a0);
s.leave();
result
}
pub(super) fn case_407_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fchoose_5fsingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fsets_2dchoose_2dsingleton(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_101_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_404_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_405_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_406_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_407_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dminus_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_set_2eminus, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_set_2eempty, &[v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dminus_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dminus_2dself(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-minus-self"
pub fn eo__24eo_5fprog_5fsets_2dminus_2dself(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dminus_2dself(s, a0, a1);
s.leave();
result
}
pub(super) fn case_408_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fminus_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fsets_2dminus_2dself(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dunion_2dself(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dunion_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dunion_2dself(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-union-self"
pub fn eo__24eo_5fprog_5fsets_2dunion_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dunion_2dself(s, a0);
s.leave();
result
}
pub(super) fn case_409_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5funion_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fsets_2dunion_2dself(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dinter_2dself(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v5))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dinter_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dinter_2dself(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-inter-self"
pub fn eo__24eo_5fprog_5fsets_2dinter_2dself(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dinter_2dself(s, a0);
s.leave();
result
}
pub(super) fn case_410_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5finter_5fself, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fsets_2dinter_2dself(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_0_eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s: &mut Store, v9: Term, v12: Term, v7: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v9, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v7, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_set_2eis_5fempty, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_Set, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_set_2eempty, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s, v9, v12, v7)
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-is-empty-elim"
pub fn eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_411_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fis_5fempty_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fsets_2dis_2dempty_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_102_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_408_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_409_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_410_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_411_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn case_0_eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_set_2eis_5fsingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_set_2esingleton, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_set_2echoose, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v3, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn body_eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_sets-is-singleton-elim"
pub fn eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_412_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2esets_5fis_5fsingleton_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fsets_2dis_2dsingleton_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s: &mut Store, v26: Term, v27: Term) -> CheckResult<Option<Term>> {
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v28))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s: &mut Store, v4: Term, v16: Term, a1: Term, a2: Term, a0: Term, a3: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v19, a0, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v18, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v17, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s, v26, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a3 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s, v4, v16, a1, a2, a0, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-ctn-false"
pub fn eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_103_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fstr_2deq_2dctn_2dfalse(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_413_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5fctn_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_103_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s: &mut Store, v4: Term, v16: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a1 { return Ok(None); }
if v11 != a0 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s, v4, v16, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-ctn-full-false1"
pub fn eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_414_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse1, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse1(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s: &mut Store, v4: Term, v16: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
if v14 != a0 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s, v4, v16, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-ctn-full-false2"
pub fn eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_415_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5fctn_5ffull_5ffalse2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fstr_2deq_2dctn_2dfull_2dfalse2(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn cases_0_103_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_412_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_413_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_414_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_415_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_25_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_100_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_101_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_102_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_103_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s: &mut Store, v29: Term) -> CheckResult<Option<Term>> {
let v30 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s: &mut Store, v18: Term, a0: Term, v11: Term, a1: Term, v4: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a1 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s, v29)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s, v18, a0, v11, a1, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-eq-len-false"
pub fn eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_416_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5feq_5flen_5ffalse, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fstr_2deq_2dlen_2dfalse(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s: &mut Store, a0: Term, a1: Term, a2: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v14, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
if v11 != a0 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s, a0, a1, a2, v14)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-empty-str"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_104_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstr(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_417_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_104_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s: &mut Store, v28: Term, v2: Term, v27: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24seq_5fempty(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v27, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s: &mut Store, v18: Term, v15: Term, a2: Term, v8: Term, a0: Term, a1: Term, v2: Term) -> CheckResult<Option<Term>> {
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
if v15 != a2 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v22, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s, v28, v2, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v19 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s, v18, v15, a2, v8, a0, a1, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-empty-range"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_105_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2drange(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_418_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5frange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_105_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s: &mut Store, v25: Term, v29: Term, v2: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24seq_5fempty(s, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s: &mut Store, v18: Term, a1: Term, v15: Term, a0: Term, v8: Term, a2: Term, v2: Term) -> CheckResult<Option<Term>> {
if v18 != a1 { return Ok(None); }
let v20 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a0 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s, v25, v29, v2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v19 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s, v18, a1, v15, a0, v8, a2, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-empty-start"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_106_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_419_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_106_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_104_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_416_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_417_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_418_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_419_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s: &mut Store, v28: Term, v2: Term, v27: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24seq_5fempty(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v27, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s: &mut Store, v18: Term, a1: Term, v15: Term, v8: Term, a0: Term, a2: Term, v2: Term) -> CheckResult<Option<Term>> {
if v18 != a1 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v20 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v22, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s, v28, v2, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v19 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s, v18, a1, v15, v8, a0, a2, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-empty-start-neg"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_107_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fprog_5fstr_2dsubstr_2dempty_2dstart_2dneg(s, v2, v5, v8, v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v20))
}
pub(super) fn case_420_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5fempty_5fstart_5fneg, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_107_eo__24eo_5fcmd_5fstep_5fproven(s, v18, v2, v5, v8, v11)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s: &mut Store, v28: Term, a4: Term, v21: Term, v2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v28, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v21, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24seq_5fempty(s, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s: &mut Store, v18: Term, a3: Term, v15: Term, a2: Term, v8: Term, a0: Term, a1: Term, a4: Term, v2: Term) -> CheckResult<Option<Term>> {
if v18 != a3 { return Ok(None); }
if v15 != a2 { return Ok(None); }
let v20 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v20 { return Ok(None); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v22, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a3) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s, v28, a4, v21, v2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v4 else { return Ok(None); }
;
let v5 = fields[0];
let v6 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v19 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s, v18, a3, v15, a2, v8, a0, a1, a4, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-substr-start-geq-len"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn more_108_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fprog_5fstr_2dsubstr_2dsubstr_2dstart_2dgeq_2dlen(s, v2, v5, v8, v11, v14, v17, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_421_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5fsubstr_5fstart_5fgeq_5flen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v23 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_108_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v21, v2, v5, v8, v11, v14, v17)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s: &mut Store, v44: Term, a2: Term, a3: Term, v42: Term, a1: Term, v41: Term, a0: Term) -> CheckResult<Option<Term>> {
let v45 = match s.apply(v44, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v42, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v41, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v49, v52) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v53))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s: &mut Store, v33: Term, v34: Term, a1: Term, v31: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v33 != v35 { return Ok(None); }
let v36 = match s.unapply(v34) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v37, v38)) = v36 else { return Ok(None); }
;
let v39 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v37 != v39 { return Ok(None); }
if v38 != a1 { return Ok(None); }
let v40 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v40 { return Ok(None); }
let v41 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s, v44, a2, a3, v42, a1, v41, a0)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s: &mut Store, v16: Term, v18: Term, v17: Term, a3: Term, a2: Term, v14: Term, a6: Term, a1: Term, a0: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.unapply(v20) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v23 != v25 { return Ok(None); }
if v24 != a3 { return Ok(None); }
if v21 != a2 { return Ok(None); }
let v26 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v26 { return Ok(None); }
let v27 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v27 else { return Ok(None); }
;
let v28 = fields[0];
let v29 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v30, v31)) = v29 else { return Ok(None); }
;
let v32 = match s.unapply(v30) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v33, v34)) = v32 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s, v33, v34, a1, v31, a0, a2, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
let v10 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s, v16, v18, v17, a3, a2, v14, a6, a1, a0)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-eq-empty"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn more_109_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v15: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24eo_5fpf, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty(s, v2, v5, v8, v11, v25, v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn case_422_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_109_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v15, v18, v21, v2, v5, v8, v11)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s: &mut Store, v43: Term, a1: Term, v36: Term, a2: Term) -> CheckResult<Option<Term>> {
let v44 = match s.apply(v43, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v36, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v47, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v45, v49) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v50))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s: &mut Store, v32: Term, v34: Term, v33: Term, a1: Term, v26: Term, a0: Term, a2: Term) -> CheckResult<Option<Term>> {
if v32 != v34 { return Ok(None); }
if v33 != a1 { return Ok(None); }
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v35 { return Ok(None); }
let v36 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v37, v42) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s, v43, a1, v36, a2)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s: &mut Store, v18: Term, a0: Term, v11: Term, v4: Term, a4: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
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
let v34 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s, v32, v34, v33, a1, v26, a0, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s, v18, a0, v11, v4, a4, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-z-eq-empty-leq"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_110_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fstr_2dsubstr_2dz_2deq_2dempty_2dleq(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_423_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5fz_5feq_5fempty_5fleq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_110_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn cases_0_105_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_420_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_421_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_422_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_423_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s: &mut Store, a0: Term, a2: Term, v58: Term) -> CheckResult<Option<Term>> {
let v59 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v60, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v59, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v58, v63) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v64))
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s: &mut Store, v47: Term, a1: Term, v40: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if v47 != a1 { return Ok(None); }
let v49 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v49 { return Ok(None); }
let v50 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v51, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v50, v57) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s, a0, a2, v58)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s: &mut Store, v29: Term, v22: Term, a6: Term, a1: Term, a0: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v29 != v34 { return Ok(None); }
let v35 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v35 { return Ok(None); }
let v36 = match s.destruct(Constructor::eo__24eo_5fpf, a6) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v36 else { return Ok(None); }
;
let v37 = fields[0];
let v38 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v46 != v48 { return Ok(None); }
more_2_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s, v47, a1, v40, a0, a2, a3)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s: &mut Store, v4: Term, a5: Term, a3: Term, a6: Term, a1: Term, a0: Term, a2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v18 else { return Ok(None); }
;
let v19 = fields[0];
let v20 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a3 { return Ok(None); }
more_1_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s, v29, v22, a6, a1, a0, a2, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Option<Term>> {
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
if v14 != a2 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s, v4, a5, a3, a6, a1, a0, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s, a0, a1, a2, a3, a4, a5, a6) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-substr-eq-empty-leq-len"
pub fn eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s, a0, a1, a2, a3, a4, a5, a6);
s.leave();
result
}
pub(super) fn more_111_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v22: Term, v23: Term, a0: Term, v15: Term, v18: Term, v21: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
if v22 != v23 { return Ok(None); }
let v24 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fpf, &[v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__24eo_5fpf, &[v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__24eo_5fpf, &[v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24eo_5fprog_5fstr_2dsubstr_2deq_2dempty_2dleq_2dlen(s, v2, v5, v8, v11, v25, v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn case_424_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsubstr_5feq_5fempty_5fleq_5flen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_111_eo__24eo_5fcmd_5fstep_5fproven(s, v22, v23, a0, v15, v18, v21, v2, v5, v8, v11)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s: &mut Store, v15: Term, a2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v15 != a2 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s, v15, a2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-len-replace-inv"
pub fn eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_112_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dinv(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_425_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5flen_5freplace_5finv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_112_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s: &mut Store, v15: Term, a2: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v15 != a2 { return Ok(None); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2ereplace_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v17, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s, v15, a2, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-len-replace-all-inv"
pub fn eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_113_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2dlen_2dreplace_2dall_2dinv(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_426_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5flen_5freplace_5fall_5finv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_113_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v1, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v0, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-len-update-inv"
pub fn eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_427_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5flen_5fupdate_5finv, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v12 = match eo__24eo_5fprog_5fstr_2dlen_2dupdate_2dinv(s, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn cases_0_106_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_424_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_425_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_426_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_427_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dupdate_2doob(s: &mut Store, v25: Term, v29: Term, a0: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dupdate_2doob(s: &mut Store, v20: Term, v22: Term, v21: Term, a0: Term, v18: Term, a1: Term, v15: Term, v4: Term, a2: Term) -> CheckResult<Option<Term>> {
if v20 != v22 { return Ok(None); }
if v21 != a0 { return Ok(None); }
if v18 != a1 { return Ok(None); }
let v23 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v23 { return Ok(None); }
let v24 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dupdate_2doob(s, v25, v29, a0)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v14, v15)) = v13 else { return Ok(None); }
;
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dupdate_2doob(s, v20, v22, v21, a0, v18, a1, v15, v4, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dupdate_2doob(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dupdate_2doob(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-update-oob"
pub fn eo__24eo_5fprog_5fstr_2dupdate_2doob(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dupdate_2doob(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_114_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2dupdate_2doob(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_428_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fupdate_5foob, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_114_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dupdate_2drev(s: &mut Store, v39: Term, v40: Term, v38: Term, v36: Term, v32: Term, a2: Term, v30: Term, v29: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v38, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v36, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v32, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v30, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v29, v48) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v49))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dupdate_2drev(s: &mut Store, v22: Term, v28: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v22, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dupdate_2drev(s, v39, v40, v38, v36, v32, a2, v30, v29)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dupdate_2drev(s: &mut Store, v18: Term, a2: Term, v11: Term, v4: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if v18 != a2 { return Ok(None); }
let v20 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v20 { return Ok(None); }
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v21 { return Ok(None); }
let v22 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dupdate_2drev(s, v22, v28, a0, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
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
let v15 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dupdate_2drev(s, v18, a2, v11, v4, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dupdate_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dupdate_2drev(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-update-rev"
pub fn eo__24eo_5fprog_5fstr_2dupdate_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dupdate_2drev(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn more_115_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v16: Term) -> CheckResult<Option<Term>> {
let v17 = match eo__24eo_5fprog_5fstr_2dupdate_2drev(s, v2, v5, v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_429_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fupdate_5frev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_115_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v16)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s: &mut Store, v29: Term, a1: Term, a2: Term, v27: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v29, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v27, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s: &mut Store, v16: Term, v18: Term, v17: Term, a0: Term, v14: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a0 { return Ok(None); }
let v23 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a2 { return Ok(None); }
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, a0) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s, v29, a1, a2, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
let v10 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s, v16, v18, v17, a0, v14, a2, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-update-fit"
pub fn eo__24eo_5fprog_5fstr_2dupdate_2dfit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dupdate_2dfit(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_116_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fstr_2dupdate_2dfit(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_430_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fupdate_5ffit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_116_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s: &mut Store, v29: Term, a0: Term, a1: Term, v28: Term, a2: Term, a3: Term, v27: Term) -> CheckResult<Option<Term>> {
let v30 = match s.apply(v29, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v27, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_list(EvalOp::ListSingletonElim, &[v36, v39]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v35, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s: &mut Store, v16: Term, v18: Term, v17: Term, a0: Term, v14: Term, a3: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
let v19 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
if v21 != a0 { return Ok(None); }
let v23 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
if v25 != a3 { return Ok(None); }
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s, v29, a0, a1, v28, a2, a3, v27)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v9 { return Ok(None); }
let v10 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s, v16, v18, v17, a0, v14, a3, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-update-concat-fit0"
pub fn eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_117_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit0(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_431_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit0, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_117_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_107_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_428_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_429_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_430_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_431_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_26_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_104_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_105_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_106_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_107_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_4_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, v63: Term, v75: Term, a0: Term, a5: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
let v76 = match s.apply(v63, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, a5) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v81, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.builtin_list(EvalOp::ListConcat, &[v79, a1, v82]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v78, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v76, v84) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v85))
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, a0: Term, a2: Term, a3: Term, a1: Term, a4: Term, a5: Term, v63: Term) -> CheckResult<Option<Term>> {
let v64 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.builtin_list(EvalOp::ListConcat, &[v67, a1, v70]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v66, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v64, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v73, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, a5) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, v63, v75, a0, a5, a3, a1)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, v49: Term, a2: Term, v50: Term, a5: Term, a0: Term, a3: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v51 = match s.unapply(v49) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v52, v53)) = v51 else { return Ok(None); }
;
let v54 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v52 != v54 { return Ok(None); }
let v55 = match s.unapply(v53) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v56, v57)) = v55 else { return Ok(None); }
;
let v58 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v56 != v58 { return Ok(None); }
if v57 != a2 { return Ok(None); }
let v59 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
let v62 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v62 { return Ok(None); }
if v61 != a5 { return Ok(None); }
let v63 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, a0, a2, a3, a1, a4, a5, v63)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, v35: Term, v36: Term, a0: Term, v29: Term, a4: Term, a7: Term, a2: Term, a5: Term, a3: Term, a1: Term) -> CheckResult<Option<Term>> {
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
let v46 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v46 else { return Ok(None); }
;
let v47 = fields[0];
let v48 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, v49, a2, v50, a5, a0, a3, a1, a4)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, v18: Term, a0: Term, v15: Term, a1: Term, v4: Term, a4: Term, a7: Term, a2: Term, a5: Term, a3: Term) -> CheckResult<Option<Term>> {
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
more_1_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, v35, v36, a0, v29, a4, a7, a2, a5, a3, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Option<Term>> {
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
more_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, v18, a0, v15, a1, v4, a4, a7, a2, a5, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, a0, a1, a2, a3, a4, a5, a6, a7) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-update-concat-fit"
pub fn eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, a0, a1, a2, a3, a4, a5, a6, a7);
s.leave();
result
}
pub(super) fn more_118_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
let v26 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v25 != v26 { return Ok(None); }
let v27 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fpf, &[v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__24eo_5fpf, &[v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24eo_5fprog_5fstr_2dupdate_2dconcat_2dfit(s, v2, v5, v8, v11, v14, v17, v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn case_432_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fupdate_5fconcat_5ffit, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_118_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v21, v24, v2, v5, v8, v11, v14, v17)
}
pub(super) fn more_8_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v128: Term, v137: Term) -> CheckResult<Option<Term>> {
let v138 = match s.apply(v128, v137) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v138))
}
pub(super) fn more_7_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v125: Term, a3: Term, a2: Term, v120: Term, a4: Term, a5: Term, a1: Term) -> CheckResult<Option<Term>> {
let v126 = match s.apply(v125, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v126, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v120, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v129, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v131, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v133, a5) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v134, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v132, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v130, v136) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v128, v137)
}
pub(super) fn more_6_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v106: Term, v89: Term, a0: Term, a1: Term, a3: Term, a2: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v115 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v106 != v115 { return Ok(None); }
let v116 = match s.unapply(v89) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v117, v118)) = v116 else { return Ok(None); }
;
let v119 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v117 != v119 { return Ok(None); }
if v118 != a0 { return Ok(None); }
let v120 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.construct(Constructor::eo_str_2eupdate, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v122, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v123, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v121, v124) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v125, a3, a2, v120, a4, a5, a1)
}
pub(super) fn more_5_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v98: Term, a3: Term, v99: Term, a2: Term, v89: Term, a0: Term, a1: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
let v100 = match s.unapply(v98) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v101, v102)) = v100 else { return Ok(None); }
;
let v103 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v101 != v103 { return Ok(None); }
if v102 != a3 { return Ok(None); }
let v104 = match s.unapply(v99) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v105, v106)) = v104 else { return Ok(None); }
;
let v107 = match s.unapply(v105) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v108, v109)) = v107 else { return Ok(None); }
;
let v110 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v108 != v110 { return Ok(None); }
let v111 = match s.unapply(v109) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v112, v113)) = v111 else { return Ok(None); }
;
let v114 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v112 != v114 { return Ok(None); }
if v113 != a2 { return Ok(None); }
more_6_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v106, v89, a0, a1, a3, a2, a4, a5)
}
pub(super) fn more_4_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v79: Term, a5: Term, a0: Term, a3: Term, a2: Term, a1: Term, a4: Term) -> CheckResult<Option<Term>> {
let v80 = match s.unapply(v79) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v81, v82)) = v80 else { return Ok(None); }
;
let v83 = match s.unapply(v81) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v84, v85)) = v83 else { return Ok(None); }
;
let v86 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v84 != v86 { return Ok(None); }
if v85 != a5 { return Ok(None); }
let v87 = match s.unapply(v82) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v88, v89)) = v87 else { return Ok(None); }
;
let v90 = match s.unapply(v88) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v91, v92)) = v90 else { return Ok(None); }
;
let v93 = match s.unapply(v91) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v94, v95)) = v93 else { return Ok(None); }
;
let v96 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v94 != v96 { return Ok(None); }
if v95 != a0 { return Ok(None); }
let v97 = match s.unapply(v92) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v98, v99)) = v97 else { return Ok(None); }
;
more_5_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v98, a3, v99, a2, v89, a0, a1, a4, a5)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v64: Term, v66: Term, v65: Term, a4: Term, v62: Term, a0: Term, a3: Term, a9: Term, a5: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
if v64 != v66 { return Ok(None); }
if v65 != a4 { return Ok(None); }
let v67 = match s.unapply(v62) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v68, v69)) = v67 else { return Ok(None); }
;
let v70 = match s.unapply(v68) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v71, v72)) = v70 else { return Ok(None); }
;
let v73 = match s.unapply(v71) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v74, v75)) = v73 else { return Ok(None); }
;
let v76 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v74 != v76 { return Ok(None); }
if v75 != a0 { return Ok(None); }
let v77 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v72 != v77 { return Ok(None); }
if v69 != a3 { return Ok(None); }
let v78 = match s.destruct(Constructor::eo__24eo_5fpf, a9) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v78 else { return Ok(None); }
;
let v79 = fields[0];
more_4_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v79, a5, a0, a3, a2, a1, a4)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v43: Term, v29: Term, a0: Term, v22: Term, a8: Term, a4: Term, a3: Term, a9: Term, a5: Term, a2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v52 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v43 != v52 { return Ok(None); }
let v53 = match s.unapply(v29) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v54, v55)) = v53 else { return Ok(None); }
;
let v56 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v54 != v56 { return Ok(None); }
if v55 != a0 { return Ok(None); }
let v57 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v57 { return Ok(None); }
let v58 = match s.destruct(Constructor::eo__24eo_5fpf, a8) { Ok(v) => v, Err(e) => return Err(e) };
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
more_3_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v64, v66, v65, a4, v62, a0, a3, a9, a5, a2, a1)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v35: Term, a3: Term, v36: Term, a2: Term, v29: Term, a0: Term, v22: Term, a8: Term, a4: Term, a9: Term, a5: Term, a1: Term) -> CheckResult<Option<Term>> {
let v37 = match s.unapply(v35) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v38, v39)) = v37 else { return Ok(None); }
;
let v40 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v38 != v40 { return Ok(None); }
if v39 != a3 { return Ok(None); }
let v41 = match s.unapply(v36) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.unapply(v42) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v45, v46)) = v44 else { return Ok(None); }
;
let v47 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v45 != v47 { return Ok(None); }
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v49 != v51 { return Ok(None); }
if v50 != a2 { return Ok(None); }
more_2_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v43, v29, a0, v22, a8, a4, a3, a9, a5, a2, a1)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, v4: Term, a7: Term, a3: Term, a2: Term, a0: Term, a8: Term, a4: Term, a9: Term, a5: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.destruct(Constructor::eo__24eo_5fpf, a7) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v18 else { return Ok(None); }
;
let v19 = fields[0];
let v20 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
let v34 = match s.unapply(v32) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v35, v36)) = v34 else { return Ok(None); }
;
more_1_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v35, a3, v36, a2, v29, a0, v22, a8, a4, a9, a5, a1)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Option<Term>> {
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
if v14 != a3 { return Ok(None); }
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v4, a7, a3, a2, a0, a8, a4, a9, a5, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-update-in-first-concat"
pub fn eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term, a6: Term, a7: Term, a8: Term, a9: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9);
s.leave();
result
}
pub(super) fn more_120_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term, v34: Term, v36: Term, v38: Term, v40: Term) -> CheckResult<Option<Term>> {
let v41 = match eo__24eo_5fprog_5fstr_2dupdate_2din_2dfirst_2dconcat(s, v2, v5, v8, v11, v14, v17, v34, v36, v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_119_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v25: Term, a0: Term, v21: Term, v24: Term, v2: Term, v5: Term, v8: Term, v11: Term, v14: Term, v17: Term) -> CheckResult<Option<Term>> {
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
more_120_eo__24eo_5fcmd_5fstep_5fproven(s, v2, v5, v8, v11, v14, v17, v34, v36, v38, v40)
}
pub(super) fn case_433_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fupdate_5fin_5ffirst_5fconcat, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_119_eo__24eo_5fcmd_5fstep_5fproven(s, v25, a0, v21, v24, v2, v5, v8, v11, v14, v17)
}
pub(super) fn more_4_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, v76: Term, a2: Term, v73: Term, v72: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v76, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v73, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v72, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v80))
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, v67: Term, v68: Term, a2: Term, v65: Term, v40: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v69 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v67 != v69 { return Ok(None); }
if v68 != a2 { return Ok(None); }
let v70 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v65 != v70 { return Ok(None); }
let v71 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v40 != v71 { return Ok(None); }
let v72 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, v76, a2, v73, v72)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, v49: Term, v51: Term, v50: Term, a0: Term, v47: Term, a1: Term, a2: Term, v40: Term) -> CheckResult<Option<Term>> {
if v49 != v51 { return Ok(None); }
let v52 = match s.unapply(v50) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v53, v54)) = v52 else { return Ok(None); }
;
let v55 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v53 != v55 { return Ok(None); }
if v54 != a0 { return Ok(None); }
let v56 = match s.unapply(v47) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v57, v58)) = v56 else { return Ok(None); }
;
let v59 = match s.unapply(v57) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v60, v61)) = v59 else { return Ok(None); }
;
let v62 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v60 != v62 { return Ok(None); }
if v61 != a1 { return Ok(None); }
let v63 = match s.unapply(v58) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v64, v65)) = v63 else { return Ok(None); }
;
let v66 = match s.unapply(v64) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v67, v68)) = v66 else { return Ok(None); }
;
more_3_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, v67, v68, a2, v65, v40, a0, a1)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, v29: Term, v22: Term, a5: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v29 != v34 { return Ok(None); }
let v35 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v35 { return Ok(None); }
let v36 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v36 else { return Ok(None); }
;
let v37 = fields[0];
let v38 = match s.unapply(v37) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v39, v40)) = v38 else { return Ok(None); }
;
let v41 = match s.unapply(v39) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v42, v43)) = v41 else { return Ok(None); }
;
let v44 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v42 != v44 { return Ok(None); }
let v45 = match s.unapply(v43) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v46, v47)) = v45 else { return Ok(None); }
;
let v48 = match s.unapply(v46) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v49, v50)) = v48 else { return Ok(None); }
;
let v51 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, v49, v51, v50, a0, v47, a1, a2, v40)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, v4: Term, a4: Term, a2: Term, a5: Term, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v17 { return Ok(None); }
let v18 = match s.destruct(Constructor::eo__24eo_5fpf, a4) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v18 else { return Ok(None); }
;
let v19 = fields[0];
let v20 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v24, v25)) = v23 else { return Ok(None); }
;
let v26 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v26 { return Ok(None); }
let v27 = match s.unapply(v25) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v28, v29)) = v27 else { return Ok(None); }
;
let v30 = match s.unapply(v28) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v31 != v33 { return Ok(None); }
if v32 != a2 { return Ok(None); }
more_1_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, v29, v22, a5, a0, a1, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
let v16 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v16 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, v4, a4, a2, a5, a0, a1)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-len-substr-in-range"
pub fn eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_121_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v12: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24eo_5fpf, &[v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24eo_5fprog_5fstr_2dlen_2dsubstr_2din_2drange(s, v2, v5, v8, v22, v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_434_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5flen_5fsubstr_5fin_5frange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v17 = match s.destruct(Constructor::eo__24emb_5findl_2econs, v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v17 else { return Ok(None); }
;
let v18 = fields[0];
let v19 = fields[1];
let v20 = match s.construct(Constructor::eo__24emb_5findl_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v20 { return Ok(None); }
more_121_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v12, v15, v18, v2, v5, v8)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s: &mut Store, v34: Term, v43: Term) -> CheckResult<Option<Term>> {
let v44 = match s.apply(v34, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v46))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s: &mut Store, v31: Term, v33: Term, v32: Term, a2: Term, a0: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v31 != v33 { return Ok(None); }
if v32 != a2 { return Ok(None); }
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v35, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v39, v42) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s, v34, v43)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s: &mut Store, v4: Term, v16: Term, a5: Term, a0: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v29 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a0 { return Ok(None); }
let v30 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s, v31, v33, v32, a2, a0, a1, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
if v11 != a2 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s, v4, v16, a5, a0, a2, a1, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-clash"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dclash(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dclash(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_122_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fstr_2dconcat_2dclash(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_435_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5fclash, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_122_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn cases_0_108_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_432_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_433_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_434_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_435_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_3_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s: &mut Store, v54: Term, v55: Term) -> CheckResult<Option<Term>> {
let v56 = match s.apply(v54, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v56))
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s: &mut Store, v35: Term, v43: Term, a2: Term, a3: Term, v34: Term) -> CheckResult<Option<Term>> {
let v44 = match s.apply(v35, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match eo__24eo_5ftypeof(s, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match eo__24eo_5fnil(s, v48, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v47, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_list(EvalOp::ListConcat, &[v45, a3, v51]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v44, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v34, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s, v54, v55)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s: &mut Store, v31: Term, v33: Term, v32: Term, a2: Term, a0: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v31 != v33 { return Ok(None); }
if v32 != a2 { return Ok(None); }
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24eo_5fnil(s, v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v38, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_list(EvalOp::ListConcat, &[v36, a1, v42]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s, v35, v43, a2, a3, v34)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s: &mut Store, v4: Term, v16: Term, a5: Term, a0: Term, a2: Term, a1: Term, a3: Term) -> CheckResult<Option<Term>> {
if v4 != v16 { return Ok(None); }
let v17 = match s.destruct(Constructor::eo__24eo_5fpf, a5) { Ok(v) => v, Err(e) => return Err(e) };
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
let v29 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a0 { return Ok(None); }
let v30 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s, v31, v33, v32, a2, a0, a1, a3)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Option<Term>> {
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
if v11 != a2 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s, v4, v16, a5, a0, a2, a1, a3)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s, a0, a1, a2, a3, a4, a5) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-clash-rev"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term, a5: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s, a0, a1, a2, a3, a4, a5);
s.leave();
result
}
pub(super) fn more_123_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, v15: Term, v18: Term, v2: Term, v5: Term, v8: Term, v11: Term) -> CheckResult<Option<Term>> {
let v21 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24eo_5fpf, &[v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fpf, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24eo_5fprog_5fstr_2dconcat_2dclash_2drev(s, v2, v5, v8, v11, v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v25))
}
pub(super) fn case_436_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5fclash_5frev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_123_eo__24eo_5fcmd_5fstep_5fproven(s, a0, v15, v18, v2, v5, v8, v11)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s: &mut Store, v31: Term, v33: Term, v32: Term, a1: Term, a0: Term, a2: Term) -> CheckResult<Option<Term>> {
if v31 != v33 { return Ok(None); }
if v32 != a1 { return Ok(None); }
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v34, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v41, v42) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v43))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s: &mut Store, v4: Term, v16: Term, a4: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v29 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a0 { return Ok(None); }
let v30 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s, v31, v33, v32, a1, a0, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v14 != a0 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s, v4, v16, a4, a0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-clash2"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_124_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fstr_2dconcat_2dclash2(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_437_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5fclash2, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_124_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s: &mut Store, v37: Term, a2: Term, v43: Term, v36: Term, v34: Term) -> CheckResult<Option<Term>> {
let v44 = match s.builtin_list(EvalOp::ListConcat, &[v37, a2, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v36, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v34, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v46, v47) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v48))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s: &mut Store, v31: Term, v33: Term, v32: Term, a1: Term, a0: Term, a2: Term) -> CheckResult<Option<Term>> {
if v31 != v33 { return Ok(None); }
if v32 != a1 { return Ok(None); }
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24eo_5ftypeof(s, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24eo_5fnil(s, v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v39, v42) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s, v37, a2, v43, v36, v34)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s: &mut Store, v4: Term, v16: Term, a4: Term, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v29 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
if v28 != a0 { return Ok(None); }
let v30 = match s.unapply(v21) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v31, v32)) = v30 else { return Ok(None); }
;
let v33 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s, v31, v33, v32, a1, a0, a2)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
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
if v14 != a0 { return Ok(None); }
if v11 != a1 { return Ok(None); }
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s, v4, v16, a4, a0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-clash2-rev"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn more_125_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, v18: Term, a0: Term, v15: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Option<Term>> {
let v19 = match s.construct(Constructor::eo__24eo_5fpf, &[v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5fstate_5fproven_5fnth(s, a0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fpf, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24eo_5fprog_5fstr_2dconcat_2dclash2_2drev(s, v2, v5, v8, v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_438_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5fclash2_5frev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
more_125_eo__24eo_5fcmd_5fstep_5fproven(s, v18, a0, v15, v2, v5, v8)
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s: &mut Store, a3: Term, a4: Term, v23: Term, v16: Term) -> CheckResult<Option<Term>> {
let v24 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_list(EvalOp::ListSingletonElim, &[v24, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v23, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v16, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v30))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s: &mut Store, v11: Term, a3: Term, a4: Term, v10: Term, v8: Term, v0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v0, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListSingletonElim, &[v18, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v17, v22) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s, a3, a4, v23, v16)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v3, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v1, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s, v11, a3, a4, v10, v8, v0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-unify"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dunify(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dunify(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_439_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5funify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v18 = match eo__24eo_5fprog_5fstr_2dconcat_2dunify(s, v2, v5, v8, v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn cases_0_109_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_436_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_437_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_438_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_439_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s: &mut Store, v35: Term, a3: Term, a4: Term, v34: Term, v33: Term, v26: Term) -> CheckResult<Option<Term>> {
let v36 = match s.apply(v35, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, a4) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.builtin_list(EvalOp::ListSingletonElim, &[v34, v37]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v33, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v26, v39) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v40))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s: &mut Store, v15: Term, v23: Term, v13: Term, v0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v24 = match s.apply(v15, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v13, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v0, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_list(EvalOp::ListSingletonElim, &[v28, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v27, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s, v35, a3, a4, v34, v33, v26)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s: &mut Store, v3: Term, v11: Term, v1: Term, a3: Term, a0: Term, a4: Term, v0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v3, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v1, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24eo_5ftypeof(s, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match eo__24eo_5fnil(s, v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v16, a4, v22]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s, v15, v23, v13, v0, a1, a2, a3, a4)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24eo_5fnil(s, v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_list(EvalOp::ListConcat, &[v4, a2, v10]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s, v3, v11, v1, a3, a0, a4, v0, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
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
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s, a0, a1, a2, a3, a4) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-unify-rev"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term, a4: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s, a0, a1, a2, a3, a4);
s.leave();
result
}
pub(super) fn case_440_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5funify_5frev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v18 = match eo__24eo_5fprog_5fstr_2dconcat_2dunify_2drev(s, v2, v5, v8, v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s: &mut Store, v19: Term, v24: Term, v14: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v19, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v14, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s: &mut Store, v6: Term, v12: Term, v4: Term, v2: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v6, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v4, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24seq_5fempty(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListSingletonElim, &[v20, v23]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s, v19, v24, v14)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s, v6, v12, v4, v2, a1, a2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-unify-base"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_441_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5funify_5fbase, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s: &mut Store, a1: Term, a2: Term, v24: Term, v19: Term) -> CheckResult<Option<Term>> {
let v25 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_list(EvalOp::ListSingletonElim, &[v25, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v24, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v19, v30) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v31))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s: &mut Store, a1: Term, v12: Term, v11: Term, v9: Term, a2: Term, v8: Term, v6: Term, v4: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match eo__24eo_5ftypeof(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24eo_5fnil(s, v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v11, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_list(EvalOp::ListConcat, &[v9, a2, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v6, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v4, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24seq_5fempty(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s, a1, a2, v24, v19)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a3) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s, a1, v12, v11, v9, a2, v8, v6, v4, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-concat-unify-base-rev"
pub fn eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s, a0, a1, a2, a3);
s.leave();
result
}
pub(super) fn case_442_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fconcat_5funify_5fbase_5frev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v15 = match eo__24eo_5fprog_5fstr_2dconcat_2dunify_2dbase_2drev(s, v2, v5, v8, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dprefixof_2delim(s: &mut Store, v11: Term, a0: Term, v10: Term, v6: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v6, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v4, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dprefixof_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dprefixof_2delim(s, v11, a0, v10, v6, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dprefixof_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dprefixof_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-prefixof-elim"
pub fn eo__24eo_5fprog_5fstr_2dprefixof_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dprefixof_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_443_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fprefixof_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fstr_2dprefixof_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn cases_0_110_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_440_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_441_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_442_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_443_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s: &mut Store, v9: Term, v11: Term, a0: Term, v8: Term, v6: Term, v4: Term) -> CheckResult<Option<Term>> {
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v8, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v6, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v4, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2esuffixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.apply(v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v0, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s, v9, v11, a0, v8, v6, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-suffixof-elim"
pub fn eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s, a0, a1);
s.leave();
result
}
pub(super) fn case_444_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsuffixof_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v9 = match eo__24eo_5fprog_5fstr_2dsuffixof_2delim(s, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s: &mut Store, a0: Term, a1: Term, v29: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s: &mut Store, v18: Term, a0: Term, v11: Term, a1: Term, v4: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a1 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s, a0, a1, v29)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s, v18, a0, v11, a1, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-prefixof-eq"
pub fn eo__24eo_5fprog_5fstr_2dprefixof_2deq(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dprefixof_2deq(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_445_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fprefixof_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fstr_2dprefixof_2deq(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_1_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s: &mut Store, a0: Term, a1: Term, v29: Term) -> CheckResult<Option<Term>> {
let v30 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s: &mut Store, v18: Term, a0: Term, v11: Term, a1: Term, v4: Term) -> CheckResult<Option<Term>> {
if v18 != a0 { return Ok(None); }
let v20 = match s.unapply(v11) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v21, v22)) = v20 else { return Ok(None); }
;
let v23 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
if v22 != a1 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2esuffixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s, a0, a1, v29)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v16 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v17, v18)) = v16 else { return Ok(None); }
;
let v19 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v19 { return Ok(None); }
more_0_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s, v18, a0, v11, a1, v4)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-suffixof-eq"
pub fn eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_446_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fsuffixof_5feq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.destruct(Constructor::eo__24emb_5fal_2econs, a2) { Ok(v) => v, Err(e) => return Err(e) };
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
let v14 = match eo__24eo_5fprog_5fstr_2dsuffixof_2deq(s, v2, v5, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_0_eo__24eo_5fprog_5fstr_2dprefixof_2done(s: &mut Store, a0: Term, a1: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo_str_2eprefixof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v14, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v22))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2dprefixof_2done(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
if v11 != a1 { return Ok(None); }
let v13 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstr_2dprefixof_2done(s, a0, a1, v14)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2dprefixof_2done(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2dprefixof_2done(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-prefixof-one"
pub fn eo__24eo_5fprog_5fstr_2dprefixof_2done(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2dprefixof_2done(s, a0, a1, a2);
s.leave();
result
}
