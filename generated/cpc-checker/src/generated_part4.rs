//! Generated functions, module 4 of 13.
#[allow(unused_imports)]
use super::*;
use crate::*;
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
pub(super) fn more_242_eo__24str_5freduction_5fpred(s: &mut Store, v267: Term, v268: Term, v266: Term, v264: Term, v206: Term, v8: Term, v5: Term, v2: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v269 = match s.apply(v267, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.apply(v266, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v264, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v206, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.construct(Constructor::eo__24emb_5fVar, &[v276, v277]) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.apply(v275, v278) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_243_eo__24str_5freduction_5fpred(s, v279, v280, v274, v8, v5, v273, v2, v272, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_241_eo__24str_5freduction_5fpred(s: &mut Store, v256: Term, v253: Term, v244: Term, v227: Term, v207: Term, v5: Term, v206: Term, v8: Term, v2: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v257 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.construct(Constructor::eo__24emb_5fVar, &[v257, v258]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v256, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v253, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.apply(v244, v261) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v227, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v207, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.apply(v265, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_242_eo__24str_5freduction_5fpred(s, v267, v268, v266, v264, v206, v8, v5, v2, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_240_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v244: Term, v227: Term, v207: Term, v206: Term, v2: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v245 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v245, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.apply(v247, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v249, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v248, v251) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v246, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.apply(v254, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v255, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_241_eo__24str_5freduction_5fpred(s, v256, v253, v244, v227, v207, v5, v206, v8, v2, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_239_eo__24str_5freduction_5fpred(s: &mut Store, v232: Term, v231: Term, v228: Term, v8: Term, v5: Term, v227: Term, v207: Term, v206: Term, v2: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v233 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo__24emb_5fVar, &[v233, v234]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.apply(v232, v235) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v237, v238) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.apply(v239, v240) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v236, v241) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v231, v242) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v228, v243) { Ok(v) => v, Err(e) => return Err(e) };
more_240_eo__24str_5freduction_5fpred(s, v8, v5, v244, v227, v207, v206, v2, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_238_eo__24str_5freduction_5fpred(s: &mut Store, v220: Term, v5: Term, v218: Term, v209: Term, v8: Term, v207: Term, v206: Term, v2: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v221 = match s.apply(v220, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.construct(Constructor::eo__24emb_5fVar, &[v222, v223]) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.apply(v221, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.apply(v218, v225) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.apply(v209, v226) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v229, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v230, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_239_eo__24str_5freduction_5fpred(s, v232, v231, v228, v8, v5, v227, v207, v206, v2, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_237_eo__24str_5freduction_5fpred(s: &mut Store, v208: Term, v8: Term, v5: Term, v207: Term, v206: Term, v2: Term, v205: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v209 = match s.apply(v208, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v210, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v212, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.apply(v214, v215) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.apply(v213, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.apply(v211, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v219, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_238_eo__24str_5freduction_5fpred(s, v220, v5, v218, v209, v8, v207, v206, v2, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_236_eo__24str_5freduction_5fpred(s: &mut Store, v196: Term, v195: Term, v192: Term, v183: Term, v166: Term, v165: Term, v8: Term, v5: Term, v2: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v197 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo__24emb_5fVar, &[v196, v197]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v195, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.apply(v192, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v183, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v166, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.apply(v202, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.apply(v165, v204) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_237_eo__24str_5freduction_5fpred(s, v208, v8, v5, v207, v206, v2, v205, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_235_eo__24str_5freduction_5fpred(s: &mut Store, v184: Term, v8: Term, v5: Term, v183: Term, v166: Term, v165: Term, v2: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v185 = match s.apply(v184, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v186, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v188, v189) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v187, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.apply(v185, v191) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.apply(v193, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v194, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_236_eo__24str_5freduction_5fpred(s, v196, v195, v192, v183, v166, v165, v8, v5, v2, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_234_eo__24str_5freduction_5fpred(s: &mut Store, v172: Term, v171: Term, v170: Term, v167: Term, v8: Term, v5: Term, v166: Term, v165: Term, v2: Term, v164: Term, v163: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v173 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.construct(Constructor::eo__24emb_5fVar, &[v172, v173]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v171, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v176, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.apply(v178, v179) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.apply(v175, v180) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.apply(v170, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.apply(v167, v182) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_235_eo__24str_5freduction_5fpred(s, v184, v8, v5, v183, v166, v165, v2, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_233_eo__24str_5freduction_5fpred(s: &mut Store, v157: Term, v160: Term, v152: Term, v151: Term, v8: Term, v5: Term, v2: Term, v150: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v161 = match s.apply(v157, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v152, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v151, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.apply(v168, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.apply(v169, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_234_eo__24str_5freduction_5fpred(s, v172, v171, v170, v167, v8, v5, v166, v165, v2, v164, v163, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_232_eo__24str_5freduction_5fpred(s: &mut Store, v141: Term, v148: Term, v140: Term, v8: Term, v5: Term, v2: Term, v139: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v149 = match s.apply(v141, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v140, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.construct(Constructor::eo__24emb_5fVar, &[v154, v155]) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v153, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.apply(v158, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v159, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_233_eo__24str_5freduction_5fpred(s, v157, v160, v152, v151, v8, v5, v2, v150, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_231_eo__24str_5freduction_5fpred(s: &mut Store, v136: Term, v131: Term, v8: Term, v5: Term, v2: Term, v130: Term, v129: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v137 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v136, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v131, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo__24emb_5fVar, &[v143, v144]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v142, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v146, v147) { Ok(v) => v, Err(e) => return Err(e) };
more_232_eo__24str_5freduction_5fpred(s, v141, v148, v140, v8, v5, v2, v139, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_230_eo__24str_5freduction_5fpred(s: &mut Store, v123: Term, v124: Term, v101: Term, v100: Term, v8: Term, v5: Term, v2: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v125 = match s.apply(v123, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v101, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v126, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v100, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.construct(Constructor::eo__24emb_5fVar, &[v133, v134]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v132, v135) { Ok(v) => v, Err(e) => return Err(e) };
more_231_eo__24str_5freduction_5fpred(s, v136, v131, v8, v5, v2, v130, v129, v99, v88, v62, v45, v36)
}
pub(super) fn more_229_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v112: Term, v102: Term, v5: Term, v101: Term, v100: Term, v2: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v113 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v113, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v112, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v102, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v117, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v119, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v118, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v116, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_230_eo__24str_5freduction_5fpred(s, v123, v124, v101, v100, v8, v5, v2, v99, v88, v62, v45, v36)
}
pub(super) fn more_228_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v100: Term, v2: Term, v99: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v101 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v103, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v109, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v107, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v104, v111) { Ok(v) => v, Err(e) => return Err(e) };
more_229_eo__24str_5freduction_5fpred(s, v8, v112, v102, v5, v101, v100, v2, v99, v88, v62, v45, v36)
}
pub(super) fn more_227_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v88: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v89 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v93, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v90, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v89, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_228_eo__24str_5freduction_5fpred(s, v8, v5, v100, v2, v99, v88, v62, v45, v36)
}
pub(super) fn more_226_eo__24str_5freduction_5fpred(s: &mut Store, v76: Term, v8: Term, v5: Term, v75: Term, v73: Term, v63: Term, v2: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v76, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v78, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v75, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v84, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v83, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v73, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v63, v87) { Ok(v) => v, Err(e) => return Err(e) };
more_227_eo__24str_5freduction_5fpred(s, v8, v5, v2, v88, v62, v45, v36)
}
pub(super) fn more_225_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v64: Term, v63: Term, v62: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v65 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v67, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.apply(v68, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v64, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v74, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__40strings_5foccur_5findex_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_226_eo__24str_5freduction_5fpred(s, v76, v8, v5, v75, v73, v63, v2, v62, v45, v36)
}
pub(super) fn more_224_eo__24str_5freduction_5fpred(s: &mut Store, v48: Term, v52: Term, v47: Term, v8: Term, v5: Term, v2: Term, v46: Term, v45: Term, v36: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v48, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v47, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__40strings_5freplace_5fre_5fall_5fresult, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v58, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v54, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v46, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_225_eo__24str_5freduction_5fpred(s, v8, v5, v2, v64, v63, v62, v45, v36)
}
pub(super) fn more_223_eo__24str_5freduction_5fpred(s: &mut Store, v40: Term, v5: Term, v38: Term, v37: Term, v8: Term, v2: Term, v36: Term) -> CheckResult<Option<Term>> {
let v41 = match s.apply(v40, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v38, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v42, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v37, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_224_eo__24str_5freduction_5fpred(s, v48, v52, v47, v8, v5, v2, v46, v45, v36)
}
pub(super) fn more_222_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v28: Term, v27: Term, v26: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v28, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v27, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v26, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo__40strings_5fnum_5foccur_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_223_eo__24str_5freduction_5fpred(s, v40, v5, v38, v37, v8, v2, v36)
}
pub(super) fn more_221_eo__24str_5freduction_5fpred(s: &mut Store, v16: Term, v15: Term, v13: Term, v11: Term, v10: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v17 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v13, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v11, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v10, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_222_eo__24str_5freduction_5fpred(s, v8, v5, v2, v28, v27, v26)
}
pub(super) fn case_10_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2ereplace_5fre_5fall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_re_2ediff, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_221_eo__24str_5freduction_5fpred(s, v16, v15, v13, v11, v10, v8, v5, v2)
}
pub(super) fn more_280_eo__24str_5freduction_5fpred(s: &mut Store, v167: Term, v268: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v269 = match s.apply(v167, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.apply(v269, v270) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.apply(v166, v271) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.apply(v54, v272) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.apply(v38, v273) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v274))
}
pub(super) fn more_279_eo__24str_5freduction_5fpred(s: &mut Store, v234: Term, v256: Term, v213: Term, v202: Term, v193: Term, v192: Term, v191: Term, v180: Term, v179: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v257 = match s.apply(v234, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.apply(v213, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.apply(v202, v258) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.apply(v193, v259) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v192, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.apply(v261, v262) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.apply(v191, v263) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v180, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.apply(v265, v266) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.apply(v179, v267) { Ok(v) => v, Err(e) => return Err(e) };
more_280_eo__24str_5freduction_5fpred(s, v167, v268, v166, v54, v38)
}
pub(super) fn more_278_eo__24str_5freduction_5fpred(s: &mut Store, v240: Term, v244: Term, v239: Term, v237: Term, v5: Term, v236: Term, v235: Term, v234: Term, v213: Term, v202: Term, v193: Term, v192: Term, v191: Term, v180: Term, v179: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v245 = match s.apply(v240, v244) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v239, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo__24emb_5fVar, &[v247, v248]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v246, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match s.apply(v237, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.apply(v251, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.apply(v236, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.apply(v235, v253) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.apply(v254, v255) { Ok(v) => v, Err(e) => return Err(e) };
more_279_eo__24str_5freduction_5fpred(s, v234, v256, v213, v202, v193, v192, v191, v180, v179, v167, v166, v54, v38)
}
pub(super) fn more_277_eo__24str_5freduction_5fpred(s: &mut Store, v215: Term, v232: Term, v214: Term, v8: Term, v5: Term, v2: Term, v213: Term, v202: Term, v193: Term, v192: Term, v191: Term, v180: Term, v179: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v233 = match s.apply(v215, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.apply(v214, v233) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.apply(v238, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.apply(v241, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.apply(v242, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.apply(v243, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_278_eo__24str_5freduction_5fpred(s, v240, v244, v239, v237, v5, v236, v235, v234, v213, v202, v193, v192, v191, v180, v179, v167, v166, v54, v38)
}
pub(super) fn more_276_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v220: Term, v215: Term, v214: Term, v213: Term, v202: Term, v193: Term, v192: Term, v191: Term, v180: Term, v179: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v221 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.apply(v222, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v221, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.apply(v226, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v227, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match s.apply(v228, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.apply(v225, v229) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match s.apply(v224, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.apply(v220, v231) { Ok(v) => v, Err(e) => return Err(e) };
more_277_eo__24str_5freduction_5fpred(s, v215, v232, v214, v8, v5, v2, v213, v202, v193, v192, v191, v180, v179, v167, v166, v54, v38)
}
pub(super) fn more_275_eo__24str_5freduction_5fpred(s: &mut Store, v205: Term, v208: Term, v204: Term, v203: Term, v8: Term, v5: Term, v2: Term, v202: Term, v193: Term, v192: Term, v191: Term, v180: Term, v179: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v209 = match s.apply(v205, v208) { Ok(v) => v, Err(e) => return Err(e) };
let v210 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.apply(v209, v210) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.apply(v204, v211) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.apply(v203, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.construct(Constructor::eo__24emb_5fVar, &[v217, v218]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.apply(v216, v219) { Ok(v) => v, Err(e) => return Err(e) };
more_276_eo__24str_5freduction_5fpred(s, v8, v5, v2, v220, v215, v214, v213, v202, v193, v192, v191, v180, v179, v167, v166, v54, v38)
}
pub(super) fn more_274_eo__24str_5freduction_5fpred(s: &mut Store, v196: Term, v195: Term, v194: Term, v8: Term, v5: Term, v2: Term, v193: Term, v192: Term, v191: Term, v180: Term, v179: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v197 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo__24emb_5fVar, &[v196, v197]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v195, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.apply(v199, v200) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.apply(v194, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo__24emb_5fVar, &[v206, v207]) { Ok(v) => v, Err(e) => return Err(e) };
more_275_eo__24str_5freduction_5fpred(s, v205, v208, v204, v203, v8, v5, v2, v202, v193, v192, v191, v180, v179, v167, v166, v54, v38)
}
pub(super) fn more_273_eo__24str_5freduction_5fpred(s: &mut Store, v184: Term, v8: Term, v5: Term, v2: Term, v183: Term, v182: Term, v181: Term, v180: Term, v179: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v185 = match s.apply(v184, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.apply(v185, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.apply(v186, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.apply(v183, v187) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.apply(v182, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.apply(v189, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.apply(v181, v190) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_274_eo__24str_5freduction_5fpred(s, v196, v195, v194, v8, v5, v2, v193, v192, v191, v180, v179, v167, v166, v54, v38)
}
pub(super) fn more_272_eo__24str_5freduction_5fpred(s: &mut Store, v172: Term, v5: Term, v2: Term, v170: Term, v169: Term, v168: Term, v8: Term, v167: Term, v166: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v173 = match s.apply(v172, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match s.apply(v173, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.apply(v170, v174) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match s.apply(v169, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match s.apply(v176, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.apply(v168, v178) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_273_eo__24str_5freduction_5fpred(s, v184, v8, v5, v2, v183, v182, v181, v180, v179, v167, v166, v54, v38)
}
pub(super) fn more_271_eo__24str_5freduction_5fpred(s: &mut Store, v141: Term, v160: Term, v123: Term, v112: Term, v80: Term, v70: Term, v55: Term, v8: Term, v5: Term, v2: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v161 = match s.apply(v141, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.apply(v123, v161) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.apply(v112, v162) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.apply(v80, v163) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.apply(v70, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.apply(v55, v165) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match s.apply(v171, v8) { Ok(v) => v, Err(e) => return Err(e) };
more_272_eo__24str_5freduction_5fpred(s, v172, v5, v2, v170, v169, v168, v8, v167, v166, v54, v38)
}
pub(super) fn more_270_eo__24str_5freduction_5fpred(s: &mut Store, v147: Term, v148: Term, v146: Term, v144: Term, v5: Term, v143: Term, v142: Term, v141: Term, v123: Term, v112: Term, v80: Term, v70: Term, v55: Term, v8: Term, v2: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v149 = match s.construct(Constructor::eo__24emb_5fVar, &[v147, v148]) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v146, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.construct(Constructor::eo__24emb_5fVar, &[v151, v152]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.apply(v150, v153) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.apply(v144, v154) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.apply(v155, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.apply(v143, v156) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.apply(v142, v157) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.apply(v158, v159) { Ok(v) => v, Err(e) => return Err(e) };
more_271_eo__24str_5freduction_5fpred(s, v141, v160, v123, v112, v80, v70, v55, v8, v5, v2, v54, v38)
}
pub(super) fn more_269_eo__24str_5freduction_5fpred(s: &mut Store, v135: Term, v136: Term, v134: Term, v130: Term, v125: Term, v124: Term, v8: Term, v5: Term, v123: Term, v112: Term, v80: Term, v70: Term, v55: Term, v2: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v137 = match s.construct(Constructor::eo__24emb_5fVar, &[v135, v136]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v134, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v130, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v125, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v124, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v145, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_270_eo__24str_5freduction_5fpred(s, v147, v148, v146, v144, v5, v143, v142, v141, v123, v112, v80, v70, v55, v8, v2, v54, v38)
}
pub(super) fn more_268_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v124: Term, v5: Term, v123: Term, v112: Term, v80: Term, v70: Term, v55: Term, v2: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v125 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo__24emb_5fVar, &[v127, v128]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.apply(v126, v129) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.apply(v132, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.apply(v131, v133) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_269_eo__24str_5freduction_5fpred(s, v135, v136, v134, v130, v125, v124, v8, v5, v123, v112, v80, v70, v55, v2, v54, v38)
}
pub(super) fn more_267_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v112: Term, v80: Term, v70: Term, v55: Term, v2: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v113 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo__24emb_5fVar, &[v116, v117]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v115, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v119, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v114, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.apply(v113, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_268_eo__24str_5freduction_5fpred(s, v8, v124, v5, v123, v112, v80, v70, v55, v2, v54, v38)
}
pub(super) fn more_266_eo__24str_5freduction_5fpred(s: &mut Store, v100: Term, v8: Term, v99: Term, v5: Term, v2: Term, v87: Term, v82: Term, v81: Term, v80: Term, v70: Term, v55: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v101 = match s.apply(v100, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v99, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v104, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v105, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v103, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v102, v108) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v87, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v82, v110) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v81, v111) { Ok(v) => v, Err(e) => return Err(e) };
more_267_eo__24str_5freduction_5fpred(s, v8, v5, v112, v80, v70, v55, v2, v54, v38)
}
pub(super) fn more_265_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v88: Term, v87: Term, v82: Term, v81: Term, v80: Term, v70: Term, v55: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v89 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v92, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v93, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v90, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v89, v95) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v88, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_266_eo__24str_5freduction_5fpred(s, v100, v8, v99, v5, v2, v87, v82, v81, v80, v70, v55, v54, v38)
}
pub(super) fn more_264_eo__24str_5freduction_5fpred(s: &mut Store, v73: Term, v76: Term, v2: Term, v72: Term, v71: Term, v8: Term, v5: Term, v70: Term, v55: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v77 = match s.apply(v73, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v72, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v71, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo__24emb_5fVar, &[v84, v85]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v83, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_265_eo__24str_5freduction_5fpred(s, v8, v5, v2, v88, v87, v82, v81, v80, v70, v55, v54, v38)
}
pub(super) fn more_263_eo__24str_5freduction_5fpred(s: &mut Store, v63: Term, v64: Term, v62: Term, v61: Term, v56: Term, v2: Term, v8: Term, v5: Term, v55: Term, v54: Term, v38: Term) -> CheckResult<Option<Term>> {
let v65 = match s.construct(Constructor::eo__24emb_5fVar, &[v63, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v62, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v66, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v61, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v56, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo__24emb_5fVar, &[v74, v75]) { Ok(v) => v, Err(e) => return Err(e) };
more_264_eo__24str_5freduction_5fpred(s, v73, v76, v2, v72, v71, v8, v5, v70, v55, v54, v38)
}
pub(super) fn more_262_eo__24str_5freduction_5fpred(s: &mut Store, v52: Term, v2: Term, v44: Term, v8: Term, v5: Term, v38: Term) -> CheckResult<Option<Term>> {
let v53 = match s.apply(v52, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v44, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.construct(Constructor::eo__24emb_5fVar, &[v58, v59]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v57, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,108,101,110,103,116,104,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_263_eo__24str_5freduction_5fpred(s, v63, v64, v62, v61, v56, v2, v8, v5, v55, v54, v38)
}
pub(super) fn more_261_eo__24str_5freduction_5fpred(s: &mut Store, v40: Term, v5: Term, v39: Term, v8: Term, v2: Term, v38: Term) -> CheckResult<Option<Term>> {
let v41 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v39, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v46, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v45, v51) { Ok(v) => v, Err(e) => return Err(e) };
more_262_eo__24str_5freduction_5fpred(s, v52, v2, v44, v8, v5, v38)
}
pub(super) fn more_260_eo__24str_5freduction_5fpred(s: &mut Store, v8: Term, v5: Term, v2: Term, v28: Term, v27: Term) -> CheckResult<Option<Term>> {
let v29 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v29, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v28, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v27, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_261_eo__24str_5freduction_5fpred(s, v40, v5, v39, v8, v2, v38)
}
pub(super) fn more_259_eo__24str_5freduction_5fpred(s: &mut Store, v11: Term, v16: Term, v2: Term, v10: Term, v8: Term, v5: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v11, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v19, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v17, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v10, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_260_eo__24str_5freduction_5fpred(s, v8, v5, v2, v28, v27)
}
pub(super) fn case_11_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
more_259_eo__24str_5freduction_5fpred(s, v11, v16, v2, v10, v8, v5)
}
pub(super) fn cases_0_2_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_292_eo__24str_5freduction_5fpred(s: &mut Store, v50: Term, v146: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v147 = match s.apply(v50, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v38, v147) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v27, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.apply(v18, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.apply(v17, v150) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v151))
}
pub(super) fn more_291_eo__24str_5freduction_5fpred(s: &mut Store, v133: Term, v134: Term, v132: Term, v130: Term, v129: Term, v117: Term, v86: Term, v85: Term, v62: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v135 = match s.construct(Constructor::eo__24emb_5fVar, &[v133, v134]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v132, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v136, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v130, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.apply(v129, v139) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v117, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v86, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v142, v143) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.apply(v85, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.apply(v62, v145) { Ok(v) => v, Err(e) => return Err(e) };
more_292_eo__24str_5freduction_5fpred(s, v50, v146, v38, v27, v18, v17)
}
pub(super) fn more_290_eo__24str_5freduction_5fpred(s: &mut Store, v122: Term, v121: Term, v119: Term, v118: Term, v5: Term, v117: Term, v86: Term, v85: Term, v62: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v123 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.construct(Constructor::eo__24emb_5fVar, &[v122, v123]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v121, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.apply(v125, v126) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.apply(v119, v127) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v118, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.apply(v131, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_291_eo__24str_5freduction_5fpred(s, v133, v134, v132, v130, v129, v117, v86, v85, v62, v50, v38, v27, v18, v17)
}
pub(super) fn more_289_eo__24str_5freduction_5fpred(s: &mut Store, v109: Term, v110: Term, v108: Term, v106: Term, v105: Term, v93: Term, v2: Term, v5: Term, v86: Term, v85: Term, v62: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v111 = match s.construct(Constructor::eo__24emb_5fVar, &[v109, v110]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v108, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v112, v113) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v106, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v105, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v93, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_290_eo__24str_5freduction_5fpred(s, v122, v121, v119, v118, v5, v117, v86, v85, v62, v50, v38, v27, v18, v17)
}
pub(super) fn more_288_eo__24str_5freduction_5fpred(s: &mut Store, v98: Term, v97: Term, v95: Term, v94: Term, v2: Term, v93: Term, v5: Term, v86: Term, v85: Term, v62: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v99 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.construct(Constructor::eo__24emb_5fVar, &[v98, v99]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v97, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v101, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v95, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v94, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v107, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_289_eo__24str_5freduction_5fpred(s, v109, v110, v108, v106, v105, v93, v2, v5, v86, v85, v62, v50, v38, v27, v18, v17)
}
pub(super) fn more_287_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v86: Term, v85: Term, v62: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v87 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v90, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v88, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v87, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
more_288_eo__24str_5freduction_5fpred(s, v98, v97, v95, v94, v2, v93, v5, v86, v85, v62, v50, v38, v27, v18, v17)
}
pub(super) fn more_286_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v74: Term, v64: Term, v63: Term, v5: Term, v62: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v75 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v76, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__24emb_5fVar, &[v79, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v78, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v74, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v64, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v63, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_287_eo__24str_5freduction_5fpred(s, v5, v2, v86, v85, v62, v50, v38, v27, v18, v17)
}
pub(super) fn more_285_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v62: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v67, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo__24emb_5fVar, &[v70, v71]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v69, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v65, v73) { Ok(v) => v, Err(e) => return Err(e) };
more_286_eo__24str_5freduction_5fpred(s, v2, v74, v64, v63, v5, v62, v50, v38, v27, v18, v17)
}
pub(super) fn more_284_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v5: Term, v50: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo__24emb_5fVar, &[v54, v55]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v53, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v57, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v52, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v51, v61) { Ok(v) => v, Err(e) => return Err(e) };
more_285_eo__24str_5freduction_5fpred(s, v5, v2, v62, v50, v38, v27, v18, v17)
}
pub(super) fn more_283_eo__24str_5freduction_5fpred(s: &mut Store, v5: Term, v2: Term, v38: Term, v27: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v39 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo__24emb_5fVar, &[v42, v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v41, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v45, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v40, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v39, v49) { Ok(v) => v, Err(e) => return Err(e) };
more_284_eo__24str_5freduction_5fpred(s, v2, v5, v50, v38, v27, v18, v17)
}
pub(super) fn more_282_eo__24str_5freduction_5fpred(s: &mut Store, v19: Term, v26: Term, v5: Term, v2: Term, v18: Term, v17: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v19, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__24emb_5fVar, &[v31, v32]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v30, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v29, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v28, v37) { Ok(v) => v, Err(e) => return Err(e) };
more_283_eo__24str_5freduction_5fpred(s, v5, v2, v38, v27, v18, v17)
}
pub(super) fn more_281_eo__24str_5freduction_5fpred(s: &mut Store, v14: Term, v2: Term, v12: Term, v11: Term, v5: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v12, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v11, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__24emb_5fVar, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_282_eo__24str_5freduction_5fpred(s, v19, v26, v5, v2, v18, v17)
}
pub(super) fn case_12_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2e_3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_281_eo__24str_5freduction_5fpred(s, v14, v2, v12, v11, v5)
}
pub(super) fn more_304_eo__24str_5freduction_5fpred(s: &mut Store, v17: Term, v144: Term, v16: Term) -> CheckResult<Option<Term>> {
let v145 = match s.apply(v17, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v145, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v16, v147) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v148))
}
pub(super) fn more_303_eo__24str_5freduction_5fpred(s: &mut Store, v129: Term, v132: Term, v127: Term, v126: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v133 = match s.apply(v129, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v133, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v127, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v126, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v70, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v54, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v139, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v53, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v37, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v26, v143) { Ok(v) => v, Err(e) => return Err(e) };
more_304_eo__24str_5freduction_5fpred(s, v17, v144, v16)
}
pub(super) fn more_302_eo__24str_5freduction_5fpred(s: &mut Store, v120: Term, v119: Term, v107: Term, v2: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v121 = match s.literal(Lit::Numeral(Integer::from(32u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v120, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v122, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v119, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v107, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo__24emb_5fVar, &[v130, v131]) { Ok(v) => v, Err(e) => return Err(e) };
more_303_eo__24str_5freduction_5fpred(s, v129, v132, v127, v126, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_301_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v108: Term, v107: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v109 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__24emb_5fVar, &[v112, v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v111, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v115, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v109, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v108, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_302_eo__24str_5freduction_5fpred(s, v120, v119, v107, v2, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_300_eo__24str_5freduction_5fpred(s: &mut Store, v96: Term, v90: Term, v89: Term, v88: Term, v87: Term, v71: Term, v2: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v97 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v90, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v89, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Numeral(Integer::from(90u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v100, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v88, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v103, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v87, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v71, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_301_eo__24str_5freduction_5fpred(s, v2, v108, v107, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_299_eo__24str_5freduction_5fpred(s: &mut Store, v76: Term, v84: Term, v75: Term, v72: Term, v2: Term, v71: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v85 = match s.apply(v76, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v75, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v72, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo__24emb_5fVar, &[v93, v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v92, v95) { Ok(v) => v, Err(e) => return Err(e) };
more_300_eo__24str_5freduction_5fpred(s, v96, v90, v89, v88, v87, v71, v2, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_298_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v72: Term, v71: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v73 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(Integer::from(65u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__24emb_5fVar, &[v79, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v78, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v82, v83) { Ok(v) => v, Err(e) => return Err(e) };
more_299_eo__24str_5freduction_5fpred(s, v76, v84, v75, v72, v2, v71, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_297_eo__24str_5freduction_5fpred(s: &mut Store, v58: Term, v60: Term, v57: Term, v56: Term, v55: Term, v2: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v57, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__24emb_5fVar, &[v63, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v62, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v66, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v56, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v55, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_298_eo__24str_5freduction_5fpred(s, v2, v72, v71, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_296_eo__24str_5freduction_5fpred(s: &mut Store, v46: Term, v48: Term, v45: Term, v44: Term, v39: Term, v38: Term, v2: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v45, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v39, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v38, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_297_eo__24str_5freduction_5fpred(s, v58, v60, v57, v56, v55, v2, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_295_eo__24str_5freduction_5fpred(s: &mut Store, v27: Term, v36: Term, v2: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v37 = match s.apply(v27, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__24emb_5fVar, &[v41, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_296_eo__24str_5freduction_5fpred(s, v46, v48, v45, v44, v39, v38, v2, v37, v26, v17, v16)
}
pub(super) fn more_294_eo__24str_5freduction_5fpred(s: &mut Store, v23: Term, v24: Term, v18: Term, v2: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v18, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24emb_5fVar, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
more_295_eo__24str_5freduction_5fpred(s, v27, v36, v2, v26, v17, v16)
}
pub(super) fn more_293_eo__24str_5freduction_5fpred(s: &mut Store, v10: Term, v12: Term, v9: Term, v8: Term, v4: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5fVar, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_294_eo__24str_5freduction_5fpred(s, v23, v24, v18, v2, v17, v16)
}
pub(super) fn case_13_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2eto_5flower, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_293_eo__24str_5freduction_5fpred(s, v10, v12, v9, v8, v4, v2)
}
pub(super) fn more_316_eo__24str_5freduction_5fpred(s: &mut Store, v17: Term, v144: Term, v16: Term) -> CheckResult<Option<Term>> {
let v145 = match s.apply(v17, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.apply(v145, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.apply(v16, v147) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v148))
}
pub(super) fn more_315_eo__24str_5freduction_5fpred(s: &mut Store, v129: Term, v132: Term, v127: Term, v126: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v133 = match s.apply(v129, v132) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.apply(v133, v134) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.apply(v127, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.apply(v126, v136) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v70, v137) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match s.apply(v54, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.apply(v139, v140) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v53, v141) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match s.apply(v37, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.apply(v26, v143) { Ok(v) => v, Err(e) => return Err(e) };
more_316_eo__24str_5freduction_5fpred(s, v17, v144, v16)
}
pub(super) fn more_314_eo__24str_5freduction_5fpred(s: &mut Store, v120: Term, v119: Term, v107: Term, v2: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v121 = match s.literal(Lit::Numeral(Integer::from(32u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v120, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.apply(v122, v123) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v119, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match s.apply(v107, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v128, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.construct(Constructor::eo__24emb_5fVar, &[v130, v131]) { Ok(v) => v, Err(e) => return Err(e) };
more_315_eo__24str_5freduction_5fpred(s, v129, v132, v127, v126, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_313_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v108: Term, v107: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v109 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.apply(v110, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo__24emb_5fVar, &[v112, v113]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v111, v114) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.apply(v115, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.apply(v109, v117) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v108, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_314_eo__24str_5freduction_5fpred(s, v120, v119, v107, v2, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_312_eo__24str_5freduction_5fpred(s: &mut Store, v96: Term, v90: Term, v89: Term, v88: Term, v87: Term, v71: Term, v2: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v97 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.apply(v96, v97) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v90, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v89, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.literal(Lit::Numeral(Integer::from(122u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v100, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v88, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v103, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v87, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v71, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_313_eo__24str_5freduction_5fpred(s, v2, v108, v107, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_311_eo__24str_5freduction_5fpred(s: &mut Store, v76: Term, v84: Term, v75: Term, v72: Term, v2: Term, v71: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v85 = match s.apply(v76, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v75, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v72, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo__24emb_5fVar, &[v93, v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v92, v95) { Ok(v) => v, Err(e) => return Err(e) };
more_312_eo__24str_5freduction_5fpred(s, v96, v90, v89, v88, v87, v71, v2, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_310_eo__24str_5freduction_5fpred(s: &mut Store, v2: Term, v72: Term, v71: Term, v70: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v73 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.literal(Lit::Numeral(Integer::from(97u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.apply(v73, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v77, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.construct(Constructor::eo__24emb_5fVar, &[v79, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v78, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v82, v83) { Ok(v) => v, Err(e) => return Err(e) };
more_311_eo__24str_5freduction_5fpred(s, v76, v84, v75, v72, v2, v71, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_309_eo__24str_5freduction_5fpred(s: &mut Store, v58: Term, v60: Term, v57: Term, v56: Term, v55: Term, v2: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.apply(v57, v61) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo__24emb_5fVar, &[v63, v64]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v62, v65) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v66, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v56, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v55, v69) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_310_eo__24str_5freduction_5fpred(s, v2, v72, v71, v70, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_308_eo__24str_5freduction_5fpred(s: &mut Store, v46: Term, v48: Term, v45: Term, v44: Term, v39: Term, v38: Term, v2: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v45, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v39, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v38, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_309_eo__24str_5freduction_5fpred(s, v58, v60, v57, v56, v55, v2, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_307_eo__24str_5freduction_5fpred(s: &mut Store, v27: Term, v36: Term, v2: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v37 = match s.apply(v27, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__24emb_5fVar, &[v41, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_308_eo__24str_5freduction_5fpred(s, v46, v48, v45, v44, v39, v38, v2, v37, v26, v17, v16)
}
pub(super) fn more_306_eo__24str_5freduction_5fpred(s: &mut Store, v23: Term, v24: Term, v18: Term, v2: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v18, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24emb_5fVar, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
more_307_eo__24str_5freduction_5fpred(s, v27, v36, v2, v26, v17, v16)
}
pub(super) fn more_305_eo__24str_5freduction_5fpred(s: &mut Store, v10: Term, v12: Term, v9: Term, v8: Term, v4: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5fVar, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_306_eo__24str_5freduction_5fpred(s, v23, v24, v18, v2, v17, v16)
}
pub(super) fn case_14_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2eto_5fupper, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_305_eo__24str_5freduction_5fpred(s, v10, v12, v9, v8, v4, v2)
}
pub(super) fn more_324_eo__24str_5freduction_5fpred(s: &mut Store, v17: Term, v96: Term, v16: Term) -> CheckResult<Option<Term>> {
let v97 = match s.apply(v17, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.apply(v97, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v16, v99) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v100))
}
pub(super) fn more_323_eo__24str_5freduction_5fpred(s: &mut Store, v79: Term, v84: Term, v74: Term, v70: Term, v68: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v85 = match s.apply(v79, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v74, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v70, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v87, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v68, v89) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.apply(v54, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v91, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v53, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v37, v94) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v26, v95) { Ok(v) => v, Err(e) => return Err(e) };
more_324_eo__24str_5freduction_5fpred(s, v17, v96, v16)
}
pub(super) fn more_322_eo__24str_5freduction_5fpred(s: &mut Store, v72: Term, v2: Term, v71: Term, v70: Term, v68: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v73 = match s.apply(v72, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v71, v73) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__24emb_5fVar, &[v76, v77]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.apply(v75, v78) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v82, v83) { Ok(v) => v, Err(e) => return Err(e) };
more_323_eo__24str_5freduction_5fpred(s, v79, v84, v74, v70, v68, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_321_eo__24str_5freduction_5fpred(s: &mut Store, v56: Term, v60: Term, v55: Term, v2: Term, v54: Term, v53: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v61 = match s.apply(v56, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__24emb_5fVar, &[v62, v63]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.apply(v61, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v65, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v55, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_322_eo__24str_5freduction_5fpred(s, v72, v2, v71, v70, v68, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_320_eo__24str_5freduction_5fpred(s: &mut Store, v46: Term, v48: Term, v45: Term, v44: Term, v39: Term, v38: Term, v2: Term, v37: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v49 = match s.apply(v46, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v45, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v44, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v39, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v38, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v58, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v57, v59) { Ok(v) => v, Err(e) => return Err(e) };
more_321_eo__24str_5freduction_5fpred(s, v56, v60, v55, v2, v54, v53, v37, v26, v17, v16)
}
pub(super) fn more_319_eo__24str_5freduction_5fpred(s: &mut Store, v27: Term, v36: Term, v2: Term, v26: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v37 = match s.apply(v27, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__24emb_5fVar, &[v41, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_320_eo__24str_5freduction_5fpred(s, v46, v48, v45, v44, v39, v38, v2, v37, v26, v17, v16)
}
pub(super) fn more_318_eo__24str_5freduction_5fpred(s: &mut Store, v23: Term, v24: Term, v18: Term, v2: Term, v17: Term, v16: Term) -> CheckResult<Option<Term>> {
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v18, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo__24emb_5fVar, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v29, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v28, v35) { Ok(v) => v, Err(e) => return Err(e) };
more_319_eo__24str_5freduction_5fpred(s, v27, v36, v2, v26, v17, v16)
}
pub(super) fn more_317_eo__24str_5freduction_5fpred(s: &mut Store, v10: Term, v12: Term, v9: Term, v8: Term, v4: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v9, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v8, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v4, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,115,116,114,95,105,110,100,101,120,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__24emb_5fVar, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_318_eo__24str_5freduction_5fpred(s, v23, v24, v18, v2, v17, v16)
}
pub(super) fn case_15_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2erev, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_317_eo__24str_5freduction_5fpred(s, v10, v12, v9, v8, v4, v2)
}
pub(super) fn cases_0_3_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_12_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_13_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_14_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_15_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_3_eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_reduction_pred"
pub fn eo__24str_5freduction_5fpred(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5freduction_5fpred(s, a0);
s.leave();
result
}
pub(super) fn requires_1_eo__24eo_5fprog_5fstring_5freduction(s: &mut Store, v1: Term, v2: Term, a0: Term) -> CheckResult<Term> {
if v1 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v3 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match eo__24str_5freduction_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v3, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v6, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24eo_5fprog_5fstring_5freduction(s, v5, v14)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24is_5fclosed_5frec(s, a0, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match requires_1_eo__24eo_5fprog_5fstring_5freduction(s, v1, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_reduction"
pub fn eo__24eo_5fprog_5fstring_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5freduction(s, a0);
s.leave();
result
}
pub(super) fn case_107_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5freduction, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstring_5freduction(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_26_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_104_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_105_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_106_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_107_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_2_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v34: Term, v36: Term, v33: Term, v32: Term) -> CheckResult<Option<Term>> {
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v33, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v32, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v41))
}
pub(super) fn more_1_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v2: Term, v24: Term, v22: Term) -> CheckResult<Option<Term>> {
let v25 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2efrom_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v26, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v25, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v24, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v22, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2efrom_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24mk_5fstr_5feager_5freduction(s, v34, v36, v33, v32)
}
pub(super) fn more_0_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v12: Term, v2: Term, v11: Term, v10: Term, v4: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v12, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(MAX_CODE_POINT))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Add, &[v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v18, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v10, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v4, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24mk_5fstr_5feager_5freduction(s, v2, v24, v22)
}
pub(super) fn case_0_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24mk_5fstr_5feager_5freduction(s, v12, v2, v11, v10, v4)
}
pub(super) fn more_5_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v34: Term, v36: Term, v33: Term) -> CheckResult<Option<Term>> {
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v37, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v33, v39) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v40))
}
pub(super) fn more_4_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v24: Term, v20: Term, v19: Term, v11: Term, v2: Term) -> CheckResult<Option<Term>> {
let v25 = match s.literal(Lit::Numeral(Integer::from(MAX_CODE_POINT))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Add, &[v25, v26]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v24, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v20, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v19, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v11, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24mk_5fstr_5feager_5freduction(s, v34, v36, v33)
}
pub(super) fn more_3_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v2: Term, v12: Term, v11: Term) -> CheckResult<Option<Term>> {
let v13 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v12, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__3c, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24mk_5fstr_5feager_5freduction(s, v24, v20, v19, v11, v2)
}
pub(super) fn case_1_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fcode, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v4, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24mk_5fstr_5feager_5freduction(s, v2, v12, v11)
}
pub(super) fn case_2_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v4, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn more_14_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v110: Term, v5: Term, v2: Term, v109: Term, v108: Term) -> CheckResult<Option<Term>> {
let v111 = match s.apply(v110, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v111, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.apply(v109, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v108, v113) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v114))
}
pub(super) fn more_13_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v97: Term, v98: Term, v94: Term, v90: Term, v89: Term, v88: Term, v29: Term, v27: Term, v13: Term, v11: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v99 = match s.apply(v97, v98) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.apply(v94, v99) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v90, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match eo__24eo_5ftypeof(s, v101) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match eo__24eo_5fnil(s, v89, v102) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v88, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v29, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.apply(v27, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v13, v106) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v11, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.construct(Constructor::eo_not, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24mk_5fstr_5feager_5freduction(s, v110, v5, v2, v109, v108)
}
pub(super) fn more_12_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v31: Term, v86: Term, v30: Term, v5: Term, v2: Term, v29: Term, v27: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v87 = match s.apply(v31, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.apply(v30, v87) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.apply(v91, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.apply(v92, v93) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v95, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v96, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_13_eo__24mk_5fstr_5feager_5freduction(s, v97, v98, v94, v90, v89, v88, v29, v27, v13, v11, v5, v2)
}
pub(super) fn more_11_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v64: Term, v74: Term, v63: Term, v62: Term, v2: Term, v61: Term, v57: Term, v31: Term, v30: Term, v5: Term, v29: Term, v27: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v75 = match s.apply(v64, v74) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v63, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v62, v76) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.apply(v79, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v78, v80) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v81, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v77, v83) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.apply(v61, v84) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v57, v85) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24mk_5fstr_5feager_5freduction(s, v31, v86, v30, v5, v2, v29, v27, v13, v11)
}
pub(super) fn more_10_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v5: Term, v2: Term, v62: Term, v61: Term, v57: Term, v31: Term, v30: Term, v29: Term, v27: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v63 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.apply(v66, v67) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.apply(v70, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.apply(v71, v72) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.apply(v68, v73) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24mk_5fstr_5feager_5freduction(s, v64, v74, v63, v62, v2, v61, v57, v31, v30, v5, v29, v27, v13, v11)
}
pub(super) fn more_9_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v2: Term, v50: Term, v49: Term, v33: Term, v5: Term, v31: Term, v30: Term, v29: Term, v27: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v51 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v50, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v53, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v49, v55) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v33, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.apply(v58, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24mk_5fstr_5feager_5freduction(s, v5, v2, v62, v61, v57, v31, v30, v29, v27, v13, v11)
}
pub(super) fn more_8_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v38: Term, v5: Term, v2: Term, v36: Term, v35: Term, v34: Term, v33: Term, v31: Term, v30: Term, v29: Term, v27: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v39 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v43, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v40, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v36, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v35, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v34, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24mk_5fstr_5feager_5freduction(s, v2, v50, v49, v33, v5, v31, v30, v29, v27, v13, v11)
}
pub(super) fn more_7_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v14: Term, v26: Term, v2: Term, v5: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v27 = match s.apply(v14, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v32, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24mk_5fstr_5feager_5freduction(s, v38, v5, v2, v36, v35, v34, v33, v31, v30, v29, v27, v13, v11)
}
pub(super) fn more_6_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v5: Term, v2: Term, v14: Term, v13: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.construct(Constructor::eo__40purify, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2esubstr, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v19, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v15, v25) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24mk_5fstr_5feager_5freduction(s, v14, v26, v2, v5, v13, v11)
}
pub(super) fn case_3_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_ite, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2econtains, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24mk_5fstr_5feager_5freduction(s, v5, v2, v14, v13, v11)
}
pub(super) fn cases_0_0_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_17_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v8: Term, v40: Term, v34: Term, v33: Term) -> CheckResult<Option<Term>> {
let v41 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v34, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v33, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn more_16_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v21: Term, v28: Term, v20: Term, v10: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v21, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v20, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v10, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v35, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_17_eo__24mk_5fstr_5feager_5freduction(s, v8, v40, v34, v33)
}
pub(super) fn more_15_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v12: Term, v16: Term, v11: Term, v8: Term, v5: Term, v2: Term, v10: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v22, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24mk_5fstr_5feager_5freduction(s, v21, v28, v20, v10, v8, v5, v2)
}
pub(super) fn case_4_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2eindexof, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24mk_5fstr_5feager_5freduction(s, v12, v16, v11, v8, v5, v2, v10)
}
pub(super) fn more_20_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v8: Term, v40: Term, v34: Term, v33: Term) -> CheckResult<Option<Term>> {
let v41 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v40, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v34, v43) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v33, v46) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v47))
}
pub(super) fn more_19_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v21: Term, v28: Term, v20: Term, v10: Term, v8: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v29 = match s.apply(v21, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v20, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v10, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo__3c_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v35, v39) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24mk_5fstr_5feager_5freduction(s, v8, v40, v34, v33)
}
pub(super) fn more_18_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v12: Term, v16: Term, v11: Term, v8: Term, v5: Term, v2: Term, v10: Term) -> CheckResult<Option<Term>> {
let v17 = match s.apply(v12, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v17, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v11, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v22, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24mk_5fstr_5feager_5freduction(s, v21, v28, v20, v10, v8, v5, v2)
}
pub(super) fn case_5_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.unapply(v4) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v7, v8)) = v6 else { return Ok(None); }
;
let v9 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v7 != v9 { return Ok(None); }
let v10 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_or, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2eindexof_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24mk_5fstr_5feager_5freduction(s, v12, v16, v11, v8, v5, v2, v10)
}
pub(super) fn more_21_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, v12: Term, v14: Term, v2: Term, v11: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v12, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24str_5ffixed_5flen_5fre(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v15, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v11, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_6_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__3d_3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, v5) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24mk_5fstr_5feager_5freduction(s, v12, v14, v2, v11)
}
pub(super) fn cases_0_1_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn body_eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$mk_str_eager_reduction"
pub fn eo__24mk_5fstr_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24mk_5fstr_5feager_5freduction(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fstring_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24mk_5fstr_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn body_eo__24eo_5fprog_5fstring_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstring_5feager_5freduction(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_string_eager_reduction"
pub fn eo__24eo_5fprog_5fstring_5feager_5freduction(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstring_5feager_5freduction(s, a0);
s.leave();
result
}
pub(super) fn case_108_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estring_5feager_5freduction, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstring_5feager_5freduction(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s: &mut Store, v17: Term, v18: Term, v12: Term) -> CheckResult<Term> {
if v17 != v18 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v17) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v19 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v21, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v19, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn case_0_eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.construct(Constructor::eo__40_40poly_2ezero, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn more_0_eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, v19: Term, v16: Term, v9: Term, v2: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo__40_40poly, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__40_40mon, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v25, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v30])))
}
pub(super) fn case_1_eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_0_eo__24str_5farith_5fentail_5fsimple_5frec(s, v19, v16, v9, v2)
}
// EO program "$str_arith_entail_simple_rec"
pub fn eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1049), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5farith_5fentail_5fsimple_5frec(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1049), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5farith_5fentail_5fsimple_5frec(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5farith_5fentail_5fsimple_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5farith_5fentail_5fsimple_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5farith_5fentail_5fsimple_5frec(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_2_eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
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
let v14 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_1_eo__24str_5farith_5fentail_5fsimple_5frec(s, v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v18)))
}
pub(super) fn if_1_eo__24str_5farith_5fentail_5fsimple_5frec(s: &mut Store, condition: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s: &mut Store, v12: Term) -> CheckResult<Option<Term>> {
let v16 = match eo__24get_5farith_5fpoly_5fnorm(s, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s, v17, v18, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v14 { return Ok(None); }
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v15 { return Ok(None); }
more_1_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s, v12)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-string-pred-entail"
pub fn eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s, a0);
s.leave();
result
}
pub(super) fn case_109_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fstring_5fpred_5fentail, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dstring_2dpred_2dentail(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s: &mut Store, v30: Term, v31: Term, v12: Term, v20: Term) -> CheckResult<Term> {
if v30 != v31 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v30) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v32 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v32, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v39, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v37, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
pub(super) fn case_0_eo__24str_5farith_5fentail_5fsimple_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24get_5farith_5fpoly_5fnorm(s, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn more_0_eo__24str_5farith_5fentail_5fsimple_5fpred(s: &mut Store, v13: Term, v14: Term, v10: Term, v8: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v8, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24get_5farith_5fpoly_5fnorm(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v18) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v19))
}
pub(super) fn case_1_eo__24str_5farith_5fentail_5fsimple_5fpred(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5farith_5fentail_5fsimple_5fpred(s, v13, v14, v10, v8)
}
pub(super) fn body_eo__24str_5farith_5fentail_5fsimple_5fpred(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5farith_5fentail_5fsimple_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5farith_5fentail_5fsimple_5fpred(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_arith_entail_simple_pred"
pub fn eo__24str_5farith_5fentail_5fsimple_5fpred(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5farith_5fentail_5fsimple_5fpred(s, a0);
s.leave();
result
}
pub(super) fn requires_1_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s: &mut Store, v24: Term, v25: Term, v20: Term, v12: Term) -> CheckResult<Term> {
if v24 != v25 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v24) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v26 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match requires_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s, v30, v31, v12, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
pub(super) fn case_0_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if a1 != a0 { return Ok(None); }
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn more_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, v18: Term, v22: Term, v16: Term, v12: Term) -> CheckResult<Term> {
let v23 = match s.apply(v18, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v16, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::And, &[v12, v25]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn if_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, v5: Term, v8: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v18, v22, v16, v12)
}
Some(false) => {
let v27 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, v51: Term, v8: Term, v50: Term, v41: Term) -> CheckResult<Term> {
let v52 = match s.apply(v51, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v50, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_core(EvalOp::And, &[v41, v54]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v55)
}
pub(super) fn if_3_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, v5: Term, v2: Term, v8: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v40 = match eo__24get_5farith_5fpoly_5fnorm(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v43, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v46, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v44, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v42, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v51, v8, v50, v41)
}
Some(false) => {
let v56 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.apply(v56, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v59, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v60) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v61)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term, v5: Term, v2: Term, v8: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v62 = match if_3_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, a2, v5, v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
Some(false) => {
let v63 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v63)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term, v8: Term, v5: Term, a1: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.builtin_core(EvalOp::Not, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::Eq, &[a1, v38]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match if_4_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v39, a2, v5, v2, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v64)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term, v5: Term, v8: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match if_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, a2, v5, v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
Some(false) => {
let v30 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::Eq, &[a1, v31]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match if_5_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v32, a2, v8, v5, a1, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v65)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.builtin_core(EvalOp::Eq, &[a1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match if_6_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v10, a2, v5, v8, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v66))
}
pub(super) fn more_7_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, v8: Term, v24: Term, v20: Term) -> CheckResult<Term> {
let v25 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v24, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::Or, &[v20, v28]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
pub(super) fn if_8_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, v2: Term, v5: Term, v8: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v21, v23) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v8, v24, v20)
}
Some(false) => {
let v30 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.apply(v30, v32) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v37)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v60 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term, v8: Term, v5: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v51 = match s.builtin_core(EvalOp::Not, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v51)
}
Some(false) => {
let v52 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v52, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v55, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_core(EvalOp::Eq, &[a1, v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match if_9_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v59, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v61)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_11_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, v50: Term, a2: Term, v8: Term, v5: Term, a1: Term) -> CheckResult<Term> {
let v62 = match if_10_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v50, a2, v8, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
pub(super) fn if_12_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term, v2: Term, v5: Term, v8: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v38 = match if_8_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, a2, v2, v5, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
Some(false) => {
let v39 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v39, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v46, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v42, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_core(EvalOp::Eq, &[a1, v49]) { Ok(v) => v, Err(e) => return Err(e) };
more_11_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v50, a2, v8, v5, a1)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[a1, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match if_12_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v12, a2, v2, v5, v8, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v63))
}
pub(super) fn if_13_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, v2: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::And, &[a2, v28]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
Some(false) => {
let v30 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match s.builtin_core(EvalOp::Not, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.construct(Constructor::eo__3e, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v20, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::And, &[v18, v23]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::Eq, &[a1, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match if_13_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v26, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_15_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, condition: Term, a2: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.builtin_core(EvalOp::Not, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24get_5farith_5fpoly_5fnorm(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24str_5farith_5fentail_5fsimple_5frec(s, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::And, &[v13, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
Some(false) => {
let v17 = match s.builtin_core(EvalOp::Eq, &[a1, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match if_14_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v17, a2, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_16_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, v12: Term, a2: Term, v2: Term, a1: Term) -> CheckResult<Option<Term>> {
let v33 = match if_15_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v12, a2, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn case_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2efrom_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v4, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_core(EvalOp::Eq, &[a1, v11]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v12, a2, v2, a1)
}
pub(super) fn body_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_arith_entail_is_approx_len"
pub fn eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, a0, a1, a2);
s.leave();
result
}
pub(super) fn case_1_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match eo__24str_5farith_5fentail_5fis_5fapprox_5flen(s, v2, a1, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn if_0_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, condition: Term, a2: Term, v8: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match s.builtin_core(EvalOp::Not, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v25, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v28, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24str_5farith_5fentail_5fsimple_5fpred(s, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::And, &[v24, v32]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v34)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, condition: Term, a2: Term, v8: Term, v5: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.builtin_core(EvalOp::Not, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
Some(false) => {
let v16 = match s.construct(Constructor::eo__2d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v16, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v19, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[a1, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match if_0_eo__24str_5farith_5fentail_5fis_5fapprox(s, v23, a2, v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v35)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, condition: Term, a2: Term, v8: Term, a1: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Eq, &[a1, v13]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match if_1_eo__24str_5farith_5fentail_5fis_5fapprox(s, v14, a2, v8, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_2_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.builtin_core(EvalOp::Eq, &[a1, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match if_2_eo__24str_5farith_5fentail_5fis_5fapprox(s, v11, a2, v8, a1, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v37))
}
pub(super) fn if_3_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, condition: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
Ok(a2)
}
Some(false) => {
let v6 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_3_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fint, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Numeral(Integer::from(1u32).neg())) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.builtin_core(EvalOp::Eq, &[a1, v4]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_3_eo__24str_5farith_5fentail_5fis_5fapprox(s, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn cases_0_0_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$str_arith_entail_is_approx"
pub fn eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1046), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1046), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_4_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24str_5farith_5fentail_5fis_5fapprox(s, v5, v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24str_5farith_5fentail_5fis_5fapprox(s, v2, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::And, &[v14, v15]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn case_5_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v14 { return Ok(None); }
let v15 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
more_5_eo__24str_5farith_5fentail_5fis_5fapprox(s, v19, v20, v5, v17, a2, v12)
}
pub(super) fn cases_0_1_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24str_5farith_5fentail_5fis_5fapprox(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_4_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, condition: Term, a2: Term, v12: Term, v27: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v31 = match s.builtin_core(EvalOp::Not, &[a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24str_5farith_5fentail_5fis_5fapprox(s, v12, v27, v31) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match eo__24str_5farith_5fentail_5fis_5fapprox(s, v12, v27, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24str_5farith_5fentail_5fis_5fapprox(s: &mut Store, v19: Term, v20: Term, v5: Term, v17: Term, a2: Term, v12: Term) -> CheckResult<Option<Term>> {
let v21 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
if v20 != v5 { return Ok(None); }
let v22 = match s.unapply(v17) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v23, v24)) = v22 else { return Ok(None); }
;
let v25 = match s.unapply(v23) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v26, v27)) = v25 else { return Ok(None); }
;
let v28 = match s.construct(Constructor::eo__2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v26 != v28 { return Ok(None); }
let v29 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v24 != v29 { return Ok(None); }
let v30 = match s.builtin_core(EvalOp::IsNeg, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match if_4_eo__24str_5farith_5fentail_5fis_5fapprox(s, v30, a2, v12, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn more_2_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s: &mut Store, v19: Term, v17: Term, v12: Term, v20: Term) -> CheckResult<Option<Term>> {
let v21 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v19 != v21 { return Ok(None); }
let v22 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v17 != v22 { return Ok(None); }
let v23 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24str_5farith_5fentail_5fis_5fapprox(s, v12, v20, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match requires_1_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s, v24, v25, v20, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v44))
}
pub(super) fn case_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v14 { return Ok(None); }
let v15 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.unapply(v16) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
more_2_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s, v19, v17, v12, v20)
}
pub(super) fn body_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_arith-string-pred-safe-approx"
pub fn eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s, a0);
s.leave();
result
}
pub(super) fn case_110_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2earith_5fstring_5fpred_5fsafe_5fapprox, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5farith_2dstring_2dpred_2dsafe_2dapprox(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn case_0_eo__24str_5feval_5fstr_5fin_5fre_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match eo__24re_5fnullable(s, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_1_eo__24str_5feval_5fstr_5fin_5fre_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v1)))
}
pub(super) fn case_2_eo__24str_5feval_5fstr_5fin_5fre_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24derivative(s, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v7])))
}
pub(super) fn step_eo__24str_5feval_5fstr_5fin_5fre_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5feval_5fstr_5fin_5fre_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5feval_5fstr_5fin_5fre_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5feval_5fstr_5fin_5fre_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5feval_5fstr_5fin_5fre_5frec(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5feval_5fstr_5fin_5fre_5frec(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
// EO program "$str_eval_str_in_re_rec"
pub fn eo__24str_5feval_5fstr_5fin_5fre_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1056), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5feval_5fstr_5fin_5fre_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1056), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s: &mut Store, v14: Term, v15: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v14 != v15 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v16, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24str_5fflatten(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match eo__24str_5feval_5fstr_5fin_5fre_5frec(s, v18, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
pub(super) fn requires_1_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s: &mut Store, v20: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v20 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v20) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v21 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v21, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.builtin_core(EvalOp::IsStr, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s, v14, v15, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match requires_1_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s, v20, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-eval"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2deval(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2deval(s, a0);
s.leave();
result
}
pub(super) fn case_111_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5feval, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2din_2dre_2deval(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_27_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_108_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_109_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_110_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_111_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_1_6_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match cases_0_24_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_25_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_26_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match cases_0_27_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s: &mut Store, v14: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v14 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v14) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v15 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
pub(super) fn case_0_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v3 != v5 { return Ok(None); }
let v6 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v6, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24re_5fsplit_5fstr_5fto_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
Ok(Some(a1))
}
// EO program "$re_split_str_to_re"
pub fn eo__24re_5fsplit_5fstr_5fto_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(969), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5fsplit_5fstr_5fto_5fre(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(969), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5fsplit_5fstr_5fto_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24re_5fsplit_5fstr_5fto_5fre(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24re_5fsplit_5fstr_5fto_5fre(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24re_5fsplit_5fstr_5fto_5fre(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v7, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24re_5fsplit_5fstr_5fto_5fre(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v10, v11) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v12))
}
pub(super) fn more_2_eo__24re_5fflatten(s: &mut Store, v11: Term, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_4_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v5, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24str_5fflatten(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24re_5fsplit_5fstr_5fto_5fre(s, v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_6_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn case_7_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v1 { return Ok(None); }
let v2 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
pub(super) fn more_3_eo__24re_5fflatten(s: &mut Store, v11: Term, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn more_4_eo__24re_5fflatten(s: &mut Store, v11: Term, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_11_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
// EO program "$re_flatten"
pub fn eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(964), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5fflatten(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(964), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v12, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24str_5fflatten(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24re_5fflatten(s, v3, v14)
}
pub(super) fn case_2_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24re_5fflatten(s, v13, v10, v16, v3, v15)
}
pub(super) fn case_3_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5fflatten(s, v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24re_5fflatten(s, v12, v3) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24re_5fflatten(s, v11, v13)
}
pub(super) fn case_5_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24re_5fflatten(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v1, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v4, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_8_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24re_5fflatten(s, v6, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_9_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5fflatten(s, v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24re_5fflatten(s, v12, v3) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24re_5fflatten(s, v11, v13)
}
pub(super) fn case_10_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5fflatten(s, v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24re_5fflatten(s, v12, v3) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24re_5fflatten(s, v11, v13)
}
pub(super) fn cases_0_0_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24re_5fflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_8_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_11_eo__24re_5fflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_0_eo__24re_5fflatten(s: &mut Store, v3: Term, v14: Term) -> CheckResult<Option<Term>> {
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24re_5fflatten(s, v15, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24re_5fsplit_5fstr_5fto_5fre(s, v14, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn more_1_eo__24re_5fflatten(s: &mut Store, v13: Term, v10: Term, v16: Term, v3: Term, v15: Term) -> CheckResult<Option<Term>> {
let v17 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v17, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24re_5fflatten(s, v16, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24re_5fflatten(s, v21, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_list(EvalOp::ListConcat, &[v15, v20, v22]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn case_0_eo__24re_5frev_5fmap_5frev(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
Ok(Some(Next::Done(a1)))
}
pub(super) fn case_0_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_1_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
pub(super) fn case_5_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
Ok(Some(a0))
}
// EO program "$re_rev_comp"
pub fn eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(967), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5frev_5fcomp(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(967), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_2_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v5, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24re_5frev_5fmap_5frev(s, v2, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v4, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v9))
}
pub(super) fn case_3_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24re_5frev_5fmap_5frev(s, v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24re_5frev_5fcomp(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_4_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24re_5frev_5fmap_5frev(s, v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v7, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24re_5frev_5fcomp(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v12, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn cases_0_0_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24re_5frev_5fcomp(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24re_5frev_5fcomp(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
// EO program "$re_rev_map_rev"
pub fn eo__24re_5frev_5fmap_5frev(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(968), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5frev_5fmap_5frev(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(968), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5frev_5fmap_5frev(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24re_5frev_5fmap_5frev(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24re_5frev_5fmap_5frev(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24re_5frev_5fmap_5frev(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24re_5frev_5fmap_5frev(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24re_5frev_5fmap_5frev(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24re_5frev_5fcomp(s, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v2, v10])))
}
pub(super) fn case_0_eo__24str_5fmembership_5fre(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
Ok(Some(v2))
}
pub(super) fn body_eo__24str_5fmembership_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fmembership_5fre(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_membership_re"
pub fn eo__24str_5fmembership_5fre(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fmembership_5fre(s, a0);
s.leave();
result
}
pub(super) fn case_0_eo__24str_5fmembership_5fstr(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
Ok(Some(v5))
}
pub(super) fn body_eo__24str_5fmembership_5fstr(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fmembership_5fstr(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_membership_str"
pub fn eo__24str_5fmembership_5fstr(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fmembership_5fstr(s, a0);
s.leave();
result
}
pub(super) fn more_0_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v16: Term, v18: Term, v5: Term, v2: Term, v9: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
if v16 != v18 { return Ok(None); }
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v21, v9, a2])))
}
pub(super) fn case_0_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5fre_5fconsume_5frec(s, v16, v18, v5, v2, v9, a2)
}
pub(super) fn if_1_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v16: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v27 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
Some(false) => {
let v28 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v33, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v32, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
None => Ok(s.stuck()),
}
}
pub(super) fn requires_4_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v32: Term, v33: Term, v5: Term, v19: Term, v16: Term) -> CheckResult<Term> {
if v32 != v33 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v32) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v34, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24str_5fflatten(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24str_5feval_5fstr_5fin_5fre_5frec(s, v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
pub(super) fn more_19_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v5: Term, v2: Term, v18: Term, v16: Term, v9: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v19 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v18, v21) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v23, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v22, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v28)))
}
pub(super) fn case_5_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24str_5fre_5fconsume_5frec(s, v5, v2, v18, v16, v9)
}
pub(super) fn case_7_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v11 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
Ok(Some(Next::Again([a0, v2, a2])))
}
pub(super) fn if_2_eo__24str_5fre_5fconsume_5finter(s: &mut Store, condition: Term, a0: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v36 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
Some(false) => {
let v37 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v40, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v38, v41) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_10_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.apply(v0, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v2)))
}
// EO program "$str_re_consume_inter"
pub fn eo__24str_5fre_5fconsume_5finter(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1080), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fconsume_5finter(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1080), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fconsume_5finter(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fconsume_5finter(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fre_5fconsume_5finter(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fre_5fconsume_5finter(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v7 { return Ok(None); }
let v8 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24str_5fre_5fconsume_5finter(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsEq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match if_4_eo__24str_5fre_5fconsume_5finter(s, v9, a0, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v45))
}
pub(super) fn if_0_eo__24str_5fre_5fconsume_5finter(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5fre_5fconsume_5finter(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fre_5fconsume_5finter(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match if_0_eo__24str_5fre_5fconsume_5finter(s, v23, a0, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24str_5fre_5fconsume_5finter(s: &mut Store, condition: Term, a0: Term, v2: Term, a2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v17 = match eo__24str_5fre_5fconsume_5finter(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::IsEq, &[v17, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match if_1_eo__24str_5fre_5fconsume_5finter(s, v19, a0, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match eo__24str_5fre_5fconsume_5finter(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_core(EvalOp::IsEq, &[v33, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match if_2_eo__24str_5fre_5fconsume_5finter(s, v35, a0, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24str_5fre_5fconsume_5finter(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24str_5fmembership_5fre(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Eq, &[v12, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_3_eo__24str_5fre_5fconsume_5finter(s, v16, a0, v2, a2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
None => Ok(s.stuck()),
}
}
// EO program "$str_re_consume_rec"
pub fn eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1081), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1081), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fconsume_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) {
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
pub(super) fn step_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match cases_0_0_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_2_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.builtin_core(EvalOp::Eq, &[v5, v16]) { Ok(v) => v, Err(e) => return Err(e) };
more_3_eo__24str_5fre_5fconsume_5frec(s, v18, v2, v9, a2, v5, v16)
}
pub(super) fn case_2_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_7_eo__24str_5fre_5fconsume_5frec(s, v5, v19, v16, v2, v9, a2)
}
pub(super) fn case_3_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v12 != v14 { return Ok(None); }
let v15 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
more_9_eo__24str_5fre_5fconsume_5frec(s, v15, v16, v2, v9, a2, v5)
}
pub(super) fn case_4_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.unapply(a2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v19, v20)) = v18 else { return Ok(None); }
;
more_17_eo__24str_5fre_5fconsume_5frec(s, v19, v5, v2, v20, v16, v9)
}
pub(super) fn case_6_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
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
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match eo__24str_5fre_5fconsume_5frec(s, v16, v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24str_5fre_5fconsume_5frec(s, v17, v5, v2, v12, a2, v9)
}
pub(super) fn case_8_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24str_5fre_5fconsume_5finter(s, a0, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn case_9_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v7, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24str_5fre_5fconsume_5funion(s, a0, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v10)))
}
pub(super) fn cases_0_0_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
if let Some(found) = match case_0_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
if let Some(found) = match case_4_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_7_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_2_eo__24str_5fre_5fconsume_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
if let Some(found) = match case_8_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_9_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_10_eo__24str_5fre_5fconsume_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_2_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v2: Term, v9: Term, a2: Term, v5: Term, v16: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match eo__24str_5fre_5fconsume_5frec(s, v2, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::IsEq, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Length, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::IsEq, &[v23, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::And, &[v22, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match if_1_eo__24str_5fre_5fconsume_5frec(s, v26, v5, v2, v16, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v39)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_3_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v18: Term, v2: Term, v9: Term, a2: Term, v5: Term, v16: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v40 = match if_2_eo__24str_5fre_5fconsume_5frec(s, v18, v2, v9, a2, v5, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v40)))
}
pub(super) fn if_5_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v2: Term, v9: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v42 = match eo__24str_5fre_5fconsume_5frec(s, v2, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v42)
}
Some(false) => {
let v43 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v19: Term, v16: Term, v2: Term, v9: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v32 = match s.builtin_core(EvalOp::IsStr, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match requires_4_eo__24str_5fre_5fconsume_5frec(s, v32, v33, v5, v19, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match if_5_eo__24str_5fre_5fconsume_5frec(s, v41, v2, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
Some(false) => {
let v45 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v46, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v45, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v51, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v50, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v49, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v56)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_7_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v5: Term, v19: Term, v16: Term, v2: Term, v9: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v21 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::IsEq, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::Length, &[v19]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::IsEq, &[v24, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::Length, &[v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::IsEq, &[v27, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_core(EvalOp::And, &[v26, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::And, &[v23, v30]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match if_6_eo__24str_5fre_5fconsume_5frec(s, v31, v5, v19, v16, v2, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v57)))
}
pub(super) fn if_8_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v2: Term, v9: Term, a2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v18 = match eo__24str_5fre_5fconsume_5frec(s, v2, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v18)
}
Some(false) => {
let v19 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v19, v22) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v24, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v23, v27) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_9_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v15: Term, v16: Term, v2: Term, v9: Term, a2: Term, v5: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v17 = match s.builtin_core(EvalOp::IsEq, &[v15, v16]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match if_8_eo__24str_5fre_5fconsume_5frec(s, v17, v2, v9, a2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v29)))
}
pub(super) fn more_10_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v96: Term, v9: Term, v92: Term, v20: Term) -> CheckResult<Term> {
let v97 = match s.apply(v96, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match eo__24str_5fre_5fconsume_5frec(s, v92, v97, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v98)
}
pub(super) fn if_11_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v16: Term, v9: Term, v23: Term, v20: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v74 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.apply(v75, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.apply(v76, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.apply(v74, v77) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.apply(v80, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v79, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match s.apply(v82, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.apply(v78, v83) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v84)
}
Some(false) => {
let v85 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v85, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match s.apply(v86, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.apply(v88, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.apply(v89, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match eo__24str_5fre_5fconsume_5frec(s, v87, v16, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match eo__24str_5fmembership_5fstr(s, v91) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.apply(v94, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.apply(v93, v95) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24str_5fre_5fconsume_5frec(s, v96, v9, v92, v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_12_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v73: Term, v5: Term, v2: Term, v16: Term, v9: Term, v23: Term, v20: Term) -> CheckResult<Term> {
let v99 = match if_11_eo__24str_5fre_5fconsume_5frec(s, v73, v5, v2, v16, v9, v23, v20) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v99)
}
pub(super) fn if_13_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v23: Term, v20: Term, v16: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v62 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.apply(v62, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v63, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.apply(v65, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match s.apply(v66, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match s.apply(v68, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.apply(v69, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24str_5fre_5fconsume_5frec(s, v67, v16, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24str_5fmembership_5fstr(s, v71) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.builtin_core(EvalOp::Eq, &[v64, v72]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24str_5fre_5fconsume_5frec(s, v73, v5, v2, v16, v9, v23, v20)
}
Some(false) => {
let v100 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match s.apply(v101, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.apply(v102, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.apply(v100, v103) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.apply(v106, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.apply(v105, v107) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.apply(v108, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.apply(v104, v109) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v110)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_14_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v23: Term, v20: Term, v9: Term, v16: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v53 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v54, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v56, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v57, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match eo__24str_5fre_5fconsume_5frec(s, v55, v9, v58) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match s.builtin_core(EvalOp::IsEq, &[v59, v60]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match if_13_eo__24str_5fre_5fconsume_5frec(s, v61, v5, v2, v23, v20, v16, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v111)
}
Some(false) => {
let v112 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.apply(v113, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.apply(v114, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v112, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match s.apply(v118, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.apply(v117, v119) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match s.apply(v120, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.apply(v116, v121) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v122)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_15_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v52: Term, v5: Term, v2: Term, v23: Term, v20: Term, v9: Term, v16: Term) -> CheckResult<Term> {
let v123 = match if_14_eo__24str_5fre_5fconsume_5frec(s, v52, v5, v2, v23, v20, v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v123)
}
pub(super) fn if_16_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v23: Term, v20: Term, v9: Term, v16: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v34, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24str_5fre_5fconsume_5frec(s, v36, v9, v39) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
Some(false) => {
let v41 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match eo__24str_5fre_5fconsume_5frec(s, v43, v16, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match eo__24str_5fmembership_5fre(s, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v49, v50) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_core(EvalOp::Eq, &[v48, v51]) { Ok(v) => v, Err(e) => return Err(e) };
more_15_eo__24str_5fre_5fconsume_5frec(s, v52, v5, v2, v23, v20, v9, v16)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_18_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v33: Term, v5: Term, v2: Term, v23: Term, v20: Term, v9: Term, v16: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v124 = match if_16_eo__24str_5fre_5fconsume_5frec(s, v33, v5, v2, v23, v20, v9, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v124)))
}
pub(super) fn more_17_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v19: Term, v5: Term, v2: Term, v20: Term, v16: Term, v9: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v29, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match eo__24str_5fre_5fconsume_5frec(s, v27, v16, v30) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.builtin_core(EvalOp::Eq, &[v31, v32]) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24str_5fre_5fconsume_5frec(s, v33, v5, v2, v23, v20, v9, v16)
}
pub(super) fn if_20_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v12: Term, a2: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v30 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24str_5fre_5fconsume_5frec(s, v32, v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24str_5fmembership_5fstr(s, v33) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match eo__24str_5fre_5fconsume_5frec(s, v34, v9, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v35)
}
Some(false) => {
let v36 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v37, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v36, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.apply(v40, v43) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_21_eo__24str_5fre_5fconsume_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v12: Term, a2: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v20 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.apply(v22, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match eo__24str_5fre_5fconsume_5frec(s, v23, v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24str_5fmembership_5fre(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v26, v27) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.builtin_core(EvalOp::IsEq, &[v25, v28]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match if_20_eo__24str_5fre_5fconsume_5frec(s, v29, v5, v2, v12, a2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v45)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_22_eo__24str_5fre_5fconsume_5frec(s: &mut Store, v17: Term, v5: Term, v2: Term, v12: Term, a2: Term, v9: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::IsEq, &[v17, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match if_21_eo__24str_5fre_5fconsume_5frec(s, v19, v5, v2, v12, a2, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v46)))
}
// EO program "$str_re_consume_union"
pub fn eo__24str_5fre_5fconsume_5funion(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1082), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fconsume_5funion(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1082), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fconsume_5funion(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fconsume_5funion(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fre_5fconsume_5funion(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fre_5fconsume_5funion(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v7 { return Ok(None); }
let v8 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v8))
}
pub(super) fn case_1_eo__24str_5fre_5fconsume_5funion(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsEq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match if_3_eo__24str_5fre_5fconsume_5funion(s, v9, a0, v2, a2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v40))
}
pub(super) fn if_0_eo__24str_5fre_5fconsume_5funion(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v26, v29) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5fre_5fconsume_5funion(s: &mut Store, condition: Term, a0: Term, v5: Term, a2: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v20 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v20)
}
Some(false) => {
let v21 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match eo__24str_5fre_5fconsume_5funion(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v21, v22]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match if_0_eo__24str_5fre_5fconsume_5funion(s, v23, a0, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5fre_5fconsume_5funion(s: &mut Store, condition: Term, a0: Term, v2: Term, a2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v17 = match eo__24str_5fre_5fconsume_5funion(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_core(EvalOp::IsEq, &[v17, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match if_1_eo__24str_5fre_5fconsume_5funion(s, v19, a0, v5, a2, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.apply(v33, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v34, v37) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v38)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24str_5fre_5fconsume_5funion(s: &mut Store, condition: Term, a0: Term, v2: Term, a2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match eo__24str_5fre_5fconsume_5funion(s, a0, v2, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match eo__24str_5fre_5fconsume_5frec(s, a0, v5, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24str_5fmembership_5fre(s, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.builtin_core(EvalOp::Eq, &[v12, v15]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match if_2_eo__24str_5fre_5fconsume_5funion(s, v16, a0, v2, a2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v39)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_0_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v66: Term, v59: Term, v65: Term) -> CheckResult<Term> {
let v67 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v67, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match eo__24str_5fflatten(s, v68) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_list(EvalOp::ListRev, &[v66, v69]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match eo__24str_5fre_5fconsume_5frec(s, v59, v65, v70) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match eo__24str_5fmembership_5fstr(s, v71) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v72)
}
pub(super) fn if_1_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v50 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v51, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match eo__24str_5fflatten(s, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.builtin_list(EvalOp::ListRev, &[v50, v53]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v54)
}
Some(false) => {
let v55 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v56, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match eo__24str_5fflatten(s, v57) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.builtin_list(EvalOp::ListRev, &[v55, v58]) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24re_5fflatten(s, v60, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.apply(v62, v63) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24re_5frev_5fmap_5frev(s, v61, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5fre_5fconsume(s, a0, v66, v59, v65)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_2_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v118: Term, v111: Term, v117: Term) -> CheckResult<Term> {
let v119 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v119, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match eo__24str_5fflatten(s, v120) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match s.builtin_list(EvalOp::ListRev, &[v118, v121]) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match eo__24str_5fre_5fconsume_5frec(s, v111, v117, v122) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match eo__24str_5fmembership_5fre(s, v123) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v124)
}
pub(super) fn if_3_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v101 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match eo__24re_5fflatten(s, v101, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v103 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.apply(v103, v104) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24re_5frev_5fmap_5frev(s, v102, v105) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v106)
}
Some(false) => {
let v107 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v108, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match eo__24str_5fflatten(s, v109) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.builtin_list(EvalOp::ListRev, &[v107, v110]) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match eo__24re_5fflatten(s, v112, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v115 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.apply(v114, v115) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match eo__24re_5frev_5fmap_5frev(s, v113, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24str_5fre_5fconsume(s, a0, v118, v111, v117)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_4_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v173: Term, v166: Term, v172: Term) -> CheckResult<Term> {
let v174 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v174, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match eo__24str_5fflatten(s, v175) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListRev, &[v173, v176]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match eo__24str_5fre_5fconsume_5frec(s, v166, v172, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match eo__24str_5fmembership_5fstr(s, v178) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v179)
}
pub(super) fn if_5_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v157 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v158 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v158, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match eo__24str_5fflatten(s, v159) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match s.builtin_list(EvalOp::ListRev, &[v157, v160]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v161)
}
Some(false) => {
let v162 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v163, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match eo__24str_5fflatten(s, v164) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.builtin_list(EvalOp::ListRev, &[v162, v165]) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match eo__24re_5fflatten(s, v167, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v170 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.apply(v169, v170) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match eo__24re_5frev_5fmap_5frev(s, v168, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24str_5fre_5fconsume(s, a0, v173, v166, v172)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_6_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v230: Term, v223: Term, v229: Term) -> CheckResult<Term> {
let v231 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v231, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match eo__24str_5fflatten(s, v232) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.builtin_list(EvalOp::ListRev, &[v230, v233]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match eo__24str_5fre_5fconsume_5frec(s, v223, v229, v234) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match eo__24str_5fmembership_5fstr(s, v235) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v236)
}
pub(super) fn if_7_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v214 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v215 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v215, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match eo__24str_5fflatten(s, v216) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match s.builtin_list(EvalOp::ListRev, &[v214, v217]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v218)
}
Some(false) => {
let v219 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v220, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match eo__24str_5fflatten(s, v221) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.builtin_list(EvalOp::ListRev, &[v219, v222]) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match eo__24re_5fflatten(s, v224, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v227 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.apply(v226, v227) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match eo__24re_5frev_5fmap_5frev(s, v225, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_6_eo__24str_5fre_5fconsume(s, a0, v230, v223, v229)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_8_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v282: Term, v275: Term, v281: Term) -> CheckResult<Term> {
let v283 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v283, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match eo__24str_5fflatten(s, v284) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match s.builtin_list(EvalOp::ListRev, &[v282, v285]) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match eo__24str_5fre_5fconsume_5frec(s, v275, v281, v286) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match eo__24str_5fmembership_5fre(s, v287) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v288)
}
pub(super) fn if_9_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v265 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match eo__24re_5fflatten(s, v265, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v267 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.apply(v267, v268) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match eo__24re_5frev_5fmap_5frev(s, v266, v269) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v270)
}
Some(false) => {
let v271 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v272, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match eo__24str_5fflatten(s, v273) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.builtin_list(EvalOp::ListRev, &[v271, v274]) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match eo__24re_5fflatten(s, v276, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v279 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.apply(v278, v279) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match eo__24re_5frev_5fmap_5frev(s, v277, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_8_eo__24str_5fre_5fconsume(s, a0, v282, v275, v281)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24str_5fcollect_5fmerge(s: &mut Store, condition: Term, a0: Term, v5: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Concat, &[a0, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v13, v16) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v17)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5fcollect_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::IsStr, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match if_0_eo__24str_5fcollect_5fmerge(s, v7, a0, v5, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v18))
}
pub(super) fn case_1_eo__24str_5fcollect_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a1 != v0 { return Ok(None); }
let v1 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.apply(v1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.apply(v2, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn body_eo__24str_5fcollect_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fcollect_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fcollect_5fmerge(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_collect_merge"
pub fn eo__24str_5fcollect_5fmerge(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fcollect_5fmerge(s, a0, a1);
s.leave();
result
}
pub(super) fn requires_1_eo__24str_5fcollect(s: &mut Store, a0: Term, v1: Term) -> CheckResult<Term> {
if a0 != v1 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
Ok(a0)
}
pub(super) fn case_1_eo__24str_5fcollect(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24eo_5ftypeof(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match eo__24seq_5fempty(s, v0) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match requires_1_eo__24str_5fcollect(s, a0, v1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v2))
}
// EO program "$str_collect"
pub fn eo__24str_5fcollect(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(1051), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fcollect(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1051), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fcollect(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fcollect(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fcollect(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fcollect(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::Length, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::IsEq, &[v7, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match if_0_eo__24str_5fcollect(s, v9, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn if_0_eo__24str_5fcollect(s: &mut Store, condition: Term, v2: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match eo__24str_5fcollect(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24str_5fcollect_5fmerge(s, v5, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24str_5fcollect(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v15)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_10_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v337: Term, v330: Term, v336: Term) -> CheckResult<Term> {
let v338 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v338, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match eo__24str_5fflatten(s, v339) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.builtin_list(EvalOp::ListRev, &[v337, v340]) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match eo__24str_5fre_5fconsume_5frec(s, v330, v336, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match eo__24str_5fmembership_5fstr(s, v342) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v343)
}
pub(super) fn if_11_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v321 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v322 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v322, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match eo__24str_5fflatten(s, v323) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match s.builtin_list(EvalOp::ListRev, &[v321, v324]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v325)
}
Some(false) => {
let v326 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v327, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match eo__24str_5fflatten(s, v328) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.builtin_list(EvalOp::ListRev, &[v326, v329]) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match eo__24re_5fflatten(s, v331, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v334 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.apply(v333, v334) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match eo__24re_5frev_5fmap_5frev(s, v332, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_10_eo__24str_5fre_5fconsume(s, a0, v337, v330, v336)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_12_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v395: Term, v388: Term, v394: Term) -> CheckResult<Term> {
let v396 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v396, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match eo__24str_5fflatten(s, v397) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.builtin_list(EvalOp::ListRev, &[v395, v398]) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match eo__24str_5fre_5fconsume_5frec(s, v388, v394, v399) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match eo__24str_5fmembership_5fstr(s, v400) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v401)
}
pub(super) fn if_13_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v379 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v380 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v380, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match eo__24str_5fflatten(s, v381) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match s.builtin_list(EvalOp::ListRev, &[v379, v382]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v383)
}
Some(false) => {
let v384 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v385, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match eo__24str_5fflatten(s, v386) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.builtin_list(EvalOp::ListRev, &[v384, v387]) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match eo__24re_5fflatten(s, v389, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v392 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.apply(v391, v392) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match eo__24re_5frev_5fmap_5frev(s, v390, v393) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_12_eo__24str_5fre_5fconsume(s, a0, v395, v388, v394)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_14_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v447: Term, v440: Term, v446: Term) -> CheckResult<Term> {
let v448 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v448, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match eo__24str_5fflatten(s, v449) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match s.builtin_list(EvalOp::ListRev, &[v447, v450]) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match eo__24str_5fre_5fconsume_5frec(s, v440, v446, v451) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match eo__24str_5fmembership_5fre(s, v452) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v453)
}
pub(super) fn if_15_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v430 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match eo__24re_5fflatten(s, v430, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v432 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.apply(v432, v433) { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match eo__24re_5frev_5fmap_5frev(s, v431, v434) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v435)
}
Some(false) => {
let v436 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v437, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match eo__24str_5fflatten(s, v438) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.builtin_list(EvalOp::ListRev, &[v436, v439]) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match eo__24re_5fflatten(s, v441, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v444 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match s.apply(v443, v444) { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match eo__24re_5frev_5fmap_5frev(s, v442, v445) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_14_eo__24str_5fre_5fconsume(s, a0, v447, v440, v446)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24re_5funflatten_5fstr(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
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
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v12, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_list(EvalOp::ListConcat, &[v11, a0, v13]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([v14, v2])))
}
pub(super) fn more_0_eo__24re_5funflatten(s: &mut Store, v11: Term, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v11, v13) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_2_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
pub(super) fn case_6_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
Ok(Some(a1))
}
// EO program "$re_unflatten"
pub fn eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(970), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5funflatten(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(970), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v9, v10)) = v8 else { return Ok(None); }
;
let v11 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v12, v10]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24re_5funflatten_5fstr(s, v13, v3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn case_1_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5funflatten(s, v9, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match eo__24re_5funflatten(s, v12, v3) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24re_5funflatten(s, v11, v13)
}
pub(super) fn case_3_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24re_5funflatten(s, v7, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_list(EvalOp::ListSingletonElim, &[v6, v8]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_4_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24re_5funflatten(s, v10, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListSingletonElim, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24re_5funflatten(s, v3, v13)
}
pub(super) fn case_5_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v2, v3)) = v1 else { return Ok(None); }
;
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match eo__24re_5funflatten(s, v10, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.builtin_list(EvalOp::ListSingletonElim, &[v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v8, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24re_5funflatten(s, v3, v13)
}
pub(super) fn cases_0_0_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24re_5funflatten(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24re_5funflatten(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn more_1_eo__24re_5funflatten(s: &mut Store, v3: Term, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24re_5funflatten(s, v14, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn more_2_eo__24re_5funflatten(s: &mut Store, v3: Term, v13: Term) -> CheckResult<Option<Term>> {
let v14 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24re_5funflatten(s, v14, v3) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v13, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
// EO program "$re_unflatten_str"
pub fn eo__24re_5funflatten_5fstr(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(971), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5funflatten_5fstr(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(971), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24re_5funflatten_5fstr(s: &mut Store, mut a0: Term, mut a1: Term) -> CheckResult<Term> {
loop {
match step_eo__24re_5funflatten_5fstr(s, a0, a1) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
}
Err(e) => return Err(e),
}
}
}
pub(super) fn step_eo__24re_5funflatten_5fstr(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Next<[Term; 2]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24re_5funflatten_5fstr(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24re_5funflatten_5fstr(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn case_1_eo__24re_5funflatten_5fstr(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Next<[Term; 2]>>> {
let v0 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24str_5fcollect(s, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_list(EvalOp::ListSingletonElim, &[v2, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.apply(v1, v4) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.apply(v0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24re_5funflatten(s, v7, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v6, v8) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v9)))
}
pub(super) fn more_16_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v502: Term, v495: Term, v501: Term) -> CheckResult<Term> {
let v503 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v504 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v503, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v505 = match eo__24str_5fflatten(s, v504) { Ok(v) => v, Err(e) => return Err(e) };
let v506 = match s.builtin_list(EvalOp::ListRev, &[v502, v505]) { Ok(v) => v, Err(e) => return Err(e) };
let v507 = match eo__24str_5fre_5fconsume_5frec(s, v495, v501, v506) { Ok(v) => v, Err(e) => return Err(e) };
let v508 = match eo__24str_5fmembership_5fstr(s, v507) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v508)
}
pub(super) fn if_17_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v486 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v487 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v488 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v487, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v489 = match eo__24str_5fflatten(s, v488) { Ok(v) => v, Err(e) => return Err(e) };
let v490 = match s.builtin_list(EvalOp::ListRev, &[v486, v489]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v490)
}
Some(false) => {
let v491 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v492 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v493 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v492, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v494 = match eo__24str_5fflatten(s, v493) { Ok(v) => v, Err(e) => return Err(e) };
let v495 = match s.builtin_list(EvalOp::ListRev, &[v491, v494]) { Ok(v) => v, Err(e) => return Err(e) };
let v496 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v497 = match eo__24re_5fflatten(s, v496, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v498 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v499 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v500 = match s.apply(v498, v499) { Ok(v) => v, Err(e) => return Err(e) };
let v501 = match eo__24re_5frev_5fmap_5frev(s, v497, v500) { Ok(v) => v, Err(e) => return Err(e) };
let v502 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_16_eo__24str_5fre_5fconsume(s, a0, v502, v495, v501)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_32_eo__24str_5fre_5fconsume(s: &mut Store, v479: Term, v482: Term, v461: Term, a0: Term, v2: Term, v460: Term, v403: Term, v459: Term, v352: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v483 = match s.builtin_core(EvalOp::Eq, &[v479, v482]) { Ok(v) => v, Err(e) => return Err(e) };
let v484 = match s.builtin_core(EvalOp::Not, &[v483]) { Ok(v) => v, Err(e) => return Err(e) };
let v485 = match s.builtin_core(EvalOp::And, &[v461, v484]) { Ok(v) => v, Err(e) => return Err(e) };
let v509 = match if_17_eo__24str_5fre_5fconsume(s, v485, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v510 = match s.builtin_list(EvalOp::ListRev, &[v460, v509]) { Ok(v) => v, Err(e) => return Err(e) };
let v511 = match eo__24str_5fre_5fconsume_5frec(s, v403, v459, v510) { Ok(v) => v, Err(e) => return Err(e) };
let v512 = match eo__24str_5fmembership_5fre(s, v511) { Ok(v) => v, Err(e) => return Err(e) };
let v513 = match eo__24re_5funflatten(s, v352, v512) { Ok(v) => v, Err(e) => return Err(e) };
let v514 = match s.builtin_list(EvalOp::ListSingletonElim, &[v351, v513]) { Ok(v) => v, Err(e) => return Err(e) };
let v515 = match s.apply(v350, v514) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v515)
}
pub(super) fn more_31_eo__24str_5fre_5fconsume(s: &mut Store, v469: Term, v470: Term, v468: Term, a0: Term, v466: Term, v461: Term, v2: Term, v460: Term, v403: Term, v459: Term, v352: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v471 = match s.apply(v469, v470) { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match eo__24re_5frev_5fmap_5frev(s, v468, v471) { Ok(v) => v, Err(e) => return Err(e) };
let v473 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v474 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v475 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v474, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v476 = match eo__24str_5fflatten(s, v475) { Ok(v) => v, Err(e) => return Err(e) };
let v477 = match s.builtin_list(EvalOp::ListRev, &[v473, v476]) { Ok(v) => v, Err(e) => return Err(e) };
let v478 = match eo__24str_5fre_5fconsume_5frec(s, v466, v472, v477) { Ok(v) => v, Err(e) => return Err(e) };
let v479 = match eo__24str_5fmembership_5fre(s, v478) { Ok(v) => v, Err(e) => return Err(e) };
let v480 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v481 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v482 = match s.apply(v480, v481) { Ok(v) => v, Err(e) => return Err(e) };
more_32_eo__24str_5fre_5fconsume(s, v479, v482, v461, a0, v2, v460, v403, v459, v352, v351, v350)
}
pub(super) fn more_30_eo__24str_5fre_5fconsume(s: &mut Store, v455: Term, v458: Term, a0: Term, v2: Term, v403: Term, v352: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v459 = match eo__24re_5frev_5fmap_5frev(s, v455, v458) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v461 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v463 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v463, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match eo__24str_5fflatten(s, v464) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.builtin_list(EvalOp::ListRev, &[v462, v465]) { Ok(v) => v, Err(e) => return Err(e) };
let v467 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match eo__24re_5fflatten(s, v467, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_31_eo__24str_5fre_5fconsume(s, v469, v470, v468, a0, v466, v461, v2, v460, v403, v459, v352, v351, v350)
}
pub(super) fn more_29_eo__24str_5fre_5fconsume(s: &mut Store, v422: Term, v405: Term, v2: Term, a0: Term, v404: Term, v403: Term, v352: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v423 = match eo__24str_5fmembership_5fre(s, v422) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v426 = match s.apply(v424, v425) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match s.builtin_core(EvalOp::Eq, &[v423, v426]) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.builtin_core(EvalOp::Not, &[v427]) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.builtin_core(EvalOp::And, &[v405, v428]) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match if_15_eo__24str_5fre_5fconsume(s, v429, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v455 = match eo__24re_5fflatten(s, v404, v454) { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.apply(v456, v457) { Ok(v) => v, Err(e) => return Err(e) };
more_30_eo__24str_5fre_5fconsume(s, v455, v458, a0, v2, v403, v352, v351, v350)
}
pub(super) fn more_28_eo__24str_5fre_5fconsume(s: &mut Store, v2: Term, a0: Term, v410: Term, v405: Term, v404: Term, v403: Term, v352: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v411 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match eo__24re_5fflatten(s, v411, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.apply(v413, v414) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match eo__24re_5frev_5fmap_5frev(s, v412, v415) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v419 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v418, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match eo__24str_5fflatten(s, v419) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.builtin_list(EvalOp::ListRev, &[v417, v420]) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match eo__24str_5fre_5fconsume_5frec(s, v410, v416, v421) { Ok(v) => v, Err(e) => return Err(e) };
more_29_eo__24str_5fre_5fconsume(s, v422, v405, v2, a0, v404, v403, v352, v351, v350)
}
pub(super) fn more_27_eo__24str_5fre_5fconsume(s: &mut Store, v372: Term, v375: Term, v354: Term, a0: Term, v2: Term, v353: Term, v352: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v376 = match s.builtin_core(EvalOp::Eq, &[v372, v375]) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.builtin_core(EvalOp::Not, &[v376]) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match s.builtin_core(EvalOp::And, &[v354, v377]) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match if_13_eo__24str_5fre_5fconsume(s, v378, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.builtin_list(EvalOp::ListRev, &[v353, v402]) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v407 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v407, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match eo__24str_5fflatten(s, v408) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.builtin_list(EvalOp::ListRev, &[v406, v409]) { Ok(v) => v, Err(e) => return Err(e) };
more_28_eo__24str_5fre_5fconsume(s, v2, a0, v410, v405, v404, v403, v352, v351, v350)
}
pub(super) fn more_26_eo__24str_5fre_5fconsume(s: &mut Store, v362: Term, v363: Term, v361: Term, a0: Term, v359: Term, v354: Term, v2: Term, v353: Term, v352: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v364 = match s.apply(v362, v363) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match eo__24re_5frev_5fmap_5frev(s, v361, v364) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v367, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match eo__24str_5fflatten(s, v368) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.builtin_list(EvalOp::ListRev, &[v366, v369]) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match eo__24str_5fre_5fconsume_5frec(s, v359, v365, v370) { Ok(v) => v, Err(e) => return Err(e) };
let v372 = match eo__24str_5fmembership_5fre(s, v371) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v375 = match s.apply(v373, v374) { Ok(v) => v, Err(e) => return Err(e) };
more_27_eo__24str_5fre_5fconsume(s, v372, v375, v354, a0, v2, v353, v352, v351, v350)
}
pub(super) fn more_25_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v2: Term, v351: Term, v350: Term) -> CheckResult<Term> {
let v352 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v356, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match eo__24str_5fflatten(s, v357) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.builtin_list(EvalOp::ListRev, &[v355, v358]) { Ok(v) => v, Err(e) => return Err(e) };
let v360 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match eo__24re_5fflatten(s, v360, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_26_eo__24str_5fre_5fconsume(s, v362, v363, v361, a0, v359, v354, v2, v353, v352, v351, v350)
}
pub(super) fn more_24_eo__24str_5fre_5fconsume(s: &mut Store, v315: Term, v316: Term, v314: Term, v296: Term, a0: Term, v2: Term, v295: Term, v238: Term, v294: Term, v187: Term, v186: Term) -> CheckResult<Term> {
let v317 = match s.apply(v315, v316) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.builtin_core(EvalOp::Eq, &[v314, v317]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.builtin_core(EvalOp::Not, &[v318]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match s.builtin_core(EvalOp::And, &[v296, v319]) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match if_11_eo__24str_5fre_5fconsume(s, v320, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.builtin_list(EvalOp::ListRev, &[v295, v344]) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match eo__24str_5fre_5fconsume_5frec(s, v238, v294, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match eo__24str_5fmembership_5fstr(s, v346) { Ok(v) => v, Err(e) => return Err(e) };
let v348 = match eo__24str_5fcollect(s, v347) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.builtin_list(EvalOp::ListSingletonElim, &[v187, v348]) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.apply(v186, v349) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_25_eo__24str_5fre_5fconsume(s, a0, v2, v351, v350)
}
pub(super) fn more_23_eo__24str_5fre_5fconsume(s: &mut Store, v304: Term, v303: Term, a0: Term, v301: Term, v296: Term, v2: Term, v295: Term, v238: Term, v294: Term, v187: Term, v186: Term) -> CheckResult<Term> {
let v305 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.apply(v304, v305) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match eo__24re_5frev_5fmap_5frev(s, v303, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v309, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match eo__24str_5fflatten(s, v310) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.builtin_list(EvalOp::ListRev, &[v308, v311]) { Ok(v) => v, Err(e) => return Err(e) };
let v313 = match eo__24str_5fre_5fconsume_5frec(s, v301, v307, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match eo__24str_5fmembership_5fre(s, v313) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_24_eo__24str_5fre_5fconsume(s, v315, v316, v314, v296, a0, v2, v295, v238, v294, v187, v186)
}
pub(super) fn more_22_eo__24str_5fre_5fconsume(s: &mut Store, v291: Term, v292: Term, v290: Term, a0: Term, v2: Term, v238: Term, v187: Term, v186: Term) -> CheckResult<Term> {
let v293 = match s.apply(v291, v292) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match eo__24re_5frev_5fmap_5frev(s, v290, v293) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v298, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match eo__24str_5fflatten(s, v299) { Ok(v) => v, Err(e) => return Err(e) };
let v301 = match s.builtin_list(EvalOp::ListRev, &[v297, v300]) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match eo__24re_5fflatten(s, v302, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_23_eo__24str_5fre_5fconsume(s, v304, v303, a0, v301, v296, v2, v295, v238, v294, v187, v186)
}
pub(super) fn more_21_eo__24str_5fre_5fconsume(s: &mut Store, v245: Term, v251: Term, v256: Term, v240: Term, v2: Term, a0: Term, v239: Term, v238: Term, v187: Term, v186: Term) -> CheckResult<Term> {
let v257 = match eo__24str_5fre_5fconsume_5frec(s, v245, v251, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match eo__24str_5fmembership_5fre(s, v257) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v261 = match s.apply(v259, v260) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match s.builtin_core(EvalOp::Eq, &[v258, v261]) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.builtin_core(EvalOp::Not, &[v262]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.builtin_core(EvalOp::And, &[v240, v263]) { Ok(v) => v, Err(e) => return Err(e) };
let v289 = match if_9_eo__24str_5fre_5fconsume(s, v264, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match eo__24re_5fflatten(s, v239, v289) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_22_eo__24str_5fre_5fconsume(s, v291, v292, v290, a0, v2, v238, v187, v186)
}
pub(super) fn more_20_eo__24str_5fre_5fconsume(s: &mut Store, v241: Term, v244: Term, v2: Term, a0: Term, v240: Term, v239: Term, v238: Term, v187: Term, v186: Term) -> CheckResult<Term> {
let v245 = match s.builtin_list(EvalOp::ListRev, &[v241, v244]) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match eo__24re_5fflatten(s, v246, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.apply(v248, v249) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match eo__24re_5frev_5fmap_5frev(s, v247, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v253 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v253, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match eo__24str_5fflatten(s, v254) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.builtin_list(EvalOp::ListRev, &[v252, v255]) { Ok(v) => v, Err(e) => return Err(e) };
more_21_eo__24str_5fre_5fconsume(s, v245, v251, v256, v240, v2, a0, v239, v238, v187, v186)
}
pub(super) fn more_19_eo__24str_5fre_5fconsume(s: &mut Store, v208: Term, v209: Term, v207: Term, v189: Term, a0: Term, v2: Term, v188: Term, v187: Term, v186: Term) -> CheckResult<Term> {
let v210 = match s.apply(v208, v209) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.builtin_core(EvalOp::Eq, &[v207, v210]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_core(EvalOp::Not, &[v211]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match s.builtin_core(EvalOp::And, &[v189, v212]) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match if_7_eo__24str_5fre_5fconsume(s, v213, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.builtin_list(EvalOp::ListRev, &[v188, v237]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v241 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v242, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match eo__24str_5fflatten(s, v243) { Ok(v) => v, Err(e) => return Err(e) };
more_20_eo__24str_5fre_5fconsume(s, v241, v244, v2, a0, v240, v239, v238, v187, v186)
}
pub(super) fn more_18_eo__24str_5fre_5fconsume(s: &mut Store, v197: Term, v196: Term, a0: Term, v194: Term, v189: Term, v2: Term, v188: Term, v187: Term, v186: Term) -> CheckResult<Term> {
let v198 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.apply(v197, v198) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match eo__24re_5frev_5fmap_5frev(s, v196, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v202, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match eo__24str_5fflatten(s, v203) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.builtin_list(EvalOp::ListRev, &[v201, v204]) { Ok(v) => v, Err(e) => return Err(e) };
let v206 = match eo__24str_5fre_5fconsume_5frec(s, v194, v200, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match eo__24str_5fmembership_5fre(s, v206) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_19_eo__24str_5fre_5fconsume(s, v208, v209, v207, v189, a0, v2, v188, v187, v186)
}
pub(super) fn if_33_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v185 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v185)
}
Some(false) => {
let v186 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v191, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match eo__24str_5fflatten(s, v192) { Ok(v) => v, Err(e) => return Err(e) };
let v194 = match s.builtin_list(EvalOp::ListRev, &[v190, v193]) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match eo__24re_5fflatten(s, v195, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_18_eo__24str_5fre_5fconsume(s, v197, v196, a0, v194, v189, v2, v188, v187, v186)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_40_eo__24str_5fre_5fconsume(s: &mut Store, v154: Term, v132: Term, a0: Term, v2: Term, v131: Term, v74: Term, v130: Term) -> CheckResult<Term> {
let v155 = match s.builtin_core(EvalOp::Not, &[v154]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match s.builtin_core(EvalOp::And, &[v132, v155]) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match if_5_eo__24str_5fre_5fconsume(s, v156, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v181 = match s.builtin_list(EvalOp::ListRev, &[v131, v180]) { Ok(v) => v, Err(e) => return Err(e) };
let v182 = match eo__24str_5fre_5fconsume_5frec(s, v74, v130, v181) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.builtin_core(EvalOp::Eq, &[v182, v183]) { Ok(v) => v, Err(e) => return Err(e) };
let v516 = match if_33_eo__24str_5fre_5fconsume(s, v184, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v516)
}
pub(super) fn more_39_eo__24str_5fre_5fconsume(s: &mut Store, v139: Term, v142: Term, a0: Term, v137: Term, v132: Term, v2: Term, v131: Term, v74: Term, v130: Term) -> CheckResult<Term> {
let v143 = match eo__24re_5frev_5fmap_5frev(s, v139, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v145, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match eo__24str_5fflatten(s, v146) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.builtin_list(EvalOp::ListRev, &[v144, v147]) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match eo__24str_5fre_5fconsume_5frec(s, v137, v143, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match eo__24str_5fmembership_5fre(s, v149) { Ok(v) => v, Err(e) => return Err(e) };
let v151 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v153 = match s.apply(v151, v152) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.builtin_core(EvalOp::Eq, &[v150, v153]) { Ok(v) => v, Err(e) => return Err(e) };
more_40_eo__24str_5fre_5fconsume(s, v154, v132, a0, v2, v131, v74, v130)
}
pub(super) fn more_38_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v2: Term, v74: Term, v130: Term) -> CheckResult<Term> {
let v131 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v134, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match eo__24str_5fflatten(s, v135) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.builtin_list(EvalOp::ListRev, &[v133, v136]) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v139 = match eo__24re_5fflatten(s, v138, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.apply(v140, v141) { Ok(v) => v, Err(e) => return Err(e) };
more_39_eo__24str_5fre_5fconsume(s, v139, v142, a0, v137, v132, v2, v131, v74, v130)
}
pub(super) fn more_37_eo__24str_5fre_5fconsume(s: &mut Store, v94: Term, v76: Term, v2: Term, a0: Term, v75: Term, v74: Term) -> CheckResult<Term> {
let v95 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v97 = match s.apply(v95, v96) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match s.builtin_core(EvalOp::Eq, &[v94, v97]) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.builtin_core(EvalOp::Not, &[v98]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.builtin_core(EvalOp::And, &[v76, v99]) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match if_3_eo__24str_5fre_5fconsume(s, v100, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24re_5fflatten(s, v75, v125) { Ok(v) => v, Err(e) => return Err(e) };
let v127 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.apply(v127, v128) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match eo__24re_5frev_5fmap_5frev(s, v126, v129) { Ok(v) => v, Err(e) => return Err(e) };
more_38_eo__24str_5fre_5fconsume(s, a0, v2, v74, v130)
}
pub(super) fn more_36_eo__24str_5fre_5fconsume(s: &mut Store, v82: Term, v2: Term, a0: Term, v81: Term, v76: Term, v75: Term, v74: Term) -> CheckResult<Term> {
let v83 = match eo__24re_5fflatten(s, v82, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.apply(v84, v85) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24re_5frev_5fmap_5frev(s, v83, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v89, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v91 = match eo__24str_5fflatten(s, v90) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.builtin_list(EvalOp::ListRev, &[v88, v91]) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match eo__24str_5fre_5fconsume_5frec(s, v81, v87, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match eo__24str_5fmembership_5fre(s, v93) { Ok(v) => v, Err(e) => return Err(e) };
more_37_eo__24str_5fre_5fconsume(s, v94, v76, v2, a0, v75, v74)
}
pub(super) fn more_35_eo__24str_5fre_5fconsume(s: &mut Store, v47: Term, v25: Term, a0: Term, v2: Term, v24: Term) -> CheckResult<Term> {
let v48 = match s.builtin_core(EvalOp::Not, &[v47]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::And, &[v25, v48]) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match if_1_eo__24str_5fre_5fconsume(s, v49, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.builtin_list(EvalOp::ListRev, &[v24, v73]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v79 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v78, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match eo__24str_5fflatten(s, v79) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.builtin_list(EvalOp::ListRev, &[v77, v80]) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_36_eo__24str_5fre_5fconsume(s, v82, v2, a0, v81, v76, v75, v74)
}
pub(super) fn more_34_eo__24str_5fre_5fconsume(s: &mut Store, v32: Term, v35: Term, a0: Term, v30: Term, v25: Term, v2: Term, v24: Term) -> CheckResult<Term> {
let v36 = match eo__24re_5frev_5fmap_5frev(s, v32, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v38, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24str_5fflatten(s, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.builtin_list(EvalOp::ListRev, &[v37, v40]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match eo__24str_5fre_5fconsume_5frec(s, v30, v36, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match eo__24str_5fmembership_5fre(s, v42) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v44, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Eq, &[v43, v46]) { Ok(v) => v, Err(e) => return Err(e) };
more_35_eo__24str_5fre_5fconsume(s, v47, v25, a0, v2, v24)
}
pub(super) fn if_41_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v27, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match eo__24str_5fflatten(s, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.builtin_list(EvalOp::ListRev, &[v26, v29]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24re_5fflatten(s, v31, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.apply(v33, v34) { Ok(v) => v, Err(e) => return Err(e) };
more_34_eo__24str_5fre_5fconsume(s, v32, v35, a0, v30, v25, v2, v24)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_42_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v583: Term, v576: Term, v582: Term) -> CheckResult<Term> {
let v584 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v585 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v584, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v586 = match eo__24str_5fflatten(s, v585) { Ok(v) => v, Err(e) => return Err(e) };
let v587 = match s.builtin_list(EvalOp::ListRev, &[v583, v586]) { Ok(v) => v, Err(e) => return Err(e) };
let v588 = match eo__24str_5fre_5fconsume_5frec(s, v576, v582, v587) { Ok(v) => v, Err(e) => return Err(e) };
let v589 = match eo__24str_5fmembership_5fstr(s, v588) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v589)
}
pub(super) fn if_43_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v567 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v568 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v569 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v568, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v570 = match eo__24str_5fflatten(s, v569) { Ok(v) => v, Err(e) => return Err(e) };
let v571 = match s.builtin_list(EvalOp::ListRev, &[v567, v570]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v571)
}
Some(false) => {
let v572 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v573 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v574 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v573, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v575 = match eo__24str_5fflatten(s, v574) { Ok(v) => v, Err(e) => return Err(e) };
let v576 = match s.builtin_list(EvalOp::ListRev, &[v572, v575]) { Ok(v) => v, Err(e) => return Err(e) };
let v577 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v578 = match eo__24re_5fflatten(s, v577, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v579 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v580 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v581 = match s.apply(v579, v580) { Ok(v) => v, Err(e) => return Err(e) };
let v582 = match eo__24re_5frev_5fmap_5frev(s, v578, v581) { Ok(v) => v, Err(e) => return Err(e) };
let v583 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_42_eo__24str_5fre_5fconsume(s, a0, v583, v576, v582)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_44_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v635: Term, v628: Term, v634: Term) -> CheckResult<Term> {
let v636 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v637 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v636, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v638 = match eo__24str_5fflatten(s, v637) { Ok(v) => v, Err(e) => return Err(e) };
let v639 = match s.builtin_list(EvalOp::ListRev, &[v635, v638]) { Ok(v) => v, Err(e) => return Err(e) };
let v640 = match eo__24str_5fre_5fconsume_5frec(s, v628, v634, v639) { Ok(v) => v, Err(e) => return Err(e) };
let v641 = match eo__24str_5fmembership_5fre(s, v640) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v641)
}
pub(super) fn if_45_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v618 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v619 = match eo__24re_5fflatten(s, v618, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v620 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v621 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v622 = match s.apply(v620, v621) { Ok(v) => v, Err(e) => return Err(e) };
let v623 = match eo__24re_5frev_5fmap_5frev(s, v619, v622) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v623)
}
Some(false) => {
let v624 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v625 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v626 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v625, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v627 = match eo__24str_5fflatten(s, v626) { Ok(v) => v, Err(e) => return Err(e) };
let v628 = match s.builtin_list(EvalOp::ListRev, &[v624, v627]) { Ok(v) => v, Err(e) => return Err(e) };
let v629 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v630 = match eo__24re_5fflatten(s, v629, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v631 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v632 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v633 = match s.apply(v631, v632) { Ok(v) => v, Err(e) => return Err(e) };
let v634 = match eo__24re_5frev_5fmap_5frev(s, v630, v633) { Ok(v) => v, Err(e) => return Err(e) };
let v635 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_44_eo__24str_5fre_5fconsume(s, a0, v635, v628, v634)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_46_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v690: Term, v683: Term, v689: Term) -> CheckResult<Term> {
let v691 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v692 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v691, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v693 = match eo__24str_5fflatten(s, v692) { Ok(v) => v, Err(e) => return Err(e) };
let v694 = match s.builtin_list(EvalOp::ListRev, &[v690, v693]) { Ok(v) => v, Err(e) => return Err(e) };
let v695 = match eo__24str_5fre_5fconsume_5frec(s, v683, v689, v694) { Ok(v) => v, Err(e) => return Err(e) };
let v696 = match eo__24str_5fmembership_5fstr(s, v695) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v696)
}
pub(super) fn if_47_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v674 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v675 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v676 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v675, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v677 = match eo__24str_5fflatten(s, v676) { Ok(v) => v, Err(e) => return Err(e) };
let v678 = match s.builtin_list(EvalOp::ListRev, &[v674, v677]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v678)
}
Some(false) => {
let v679 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v680 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v681 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v680, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v682 = match eo__24str_5fflatten(s, v681) { Ok(v) => v, Err(e) => return Err(e) };
let v683 = match s.builtin_list(EvalOp::ListRev, &[v679, v682]) { Ok(v) => v, Err(e) => return Err(e) };
let v684 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v685 = match eo__24re_5fflatten(s, v684, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v686 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v687 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v688 = match s.apply(v686, v687) { Ok(v) => v, Err(e) => return Err(e) };
let v689 = match eo__24re_5frev_5fmap_5frev(s, v685, v688) { Ok(v) => v, Err(e) => return Err(e) };
let v690 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_46_eo__24str_5fre_5fconsume(s, a0, v690, v683, v689)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_48_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v747: Term, v740: Term, v746: Term) -> CheckResult<Term> {
let v748 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v749 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v748, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v750 = match eo__24str_5fflatten(s, v749) { Ok(v) => v, Err(e) => return Err(e) };
let v751 = match s.builtin_list(EvalOp::ListRev, &[v747, v750]) { Ok(v) => v, Err(e) => return Err(e) };
let v752 = match eo__24str_5fre_5fconsume_5frec(s, v740, v746, v751) { Ok(v) => v, Err(e) => return Err(e) };
let v753 = match eo__24str_5fmembership_5fstr(s, v752) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v753)
}
pub(super) fn if_49_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v731 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v732 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v733 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v732, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v734 = match eo__24str_5fflatten(s, v733) { Ok(v) => v, Err(e) => return Err(e) };
let v735 = match s.builtin_list(EvalOp::ListRev, &[v731, v734]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v735)
}
Some(false) => {
let v736 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v737 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v738 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v737, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v739 = match eo__24str_5fflatten(s, v738) { Ok(v) => v, Err(e) => return Err(e) };
let v740 = match s.builtin_list(EvalOp::ListRev, &[v736, v739]) { Ok(v) => v, Err(e) => return Err(e) };
let v741 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v742 = match eo__24re_5fflatten(s, v741, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v743 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v744 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v745 = match s.apply(v743, v744) { Ok(v) => v, Err(e) => return Err(e) };
let v746 = match eo__24re_5frev_5fmap_5frev(s, v742, v745) { Ok(v) => v, Err(e) => return Err(e) };
let v747 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_48_eo__24str_5fre_5fconsume(s, a0, v747, v740, v746)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_50_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v799: Term, v792: Term, v798: Term) -> CheckResult<Term> {
let v800 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v801 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v800, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v802 = match eo__24str_5fflatten(s, v801) { Ok(v) => v, Err(e) => return Err(e) };
let v803 = match s.builtin_list(EvalOp::ListRev, &[v799, v802]) { Ok(v) => v, Err(e) => return Err(e) };
let v804 = match eo__24str_5fre_5fconsume_5frec(s, v792, v798, v803) { Ok(v) => v, Err(e) => return Err(e) };
let v805 = match eo__24str_5fmembership_5fre(s, v804) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v805)
}
pub(super) fn if_51_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v782 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v783 = match eo__24re_5fflatten(s, v782, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v784 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v785 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v786 = match s.apply(v784, v785) { Ok(v) => v, Err(e) => return Err(e) };
let v787 = match eo__24re_5frev_5fmap_5frev(s, v783, v786) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v787)
}
Some(false) => {
let v788 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v789 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v790 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v789, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v791 = match eo__24str_5fflatten(s, v790) { Ok(v) => v, Err(e) => return Err(e) };
let v792 = match s.builtin_list(EvalOp::ListRev, &[v788, v791]) { Ok(v) => v, Err(e) => return Err(e) };
let v793 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v794 = match eo__24re_5fflatten(s, v793, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v795 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v796 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v797 = match s.apply(v795, v796) { Ok(v) => v, Err(e) => return Err(e) };
let v798 = match eo__24re_5frev_5fmap_5frev(s, v794, v797) { Ok(v) => v, Err(e) => return Err(e) };
let v799 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_50_eo__24str_5fre_5fconsume(s, a0, v799, v792, v798)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_52_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v854: Term, v847: Term, v853: Term) -> CheckResult<Term> {
let v855 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v856 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v855, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v857 = match eo__24str_5fflatten(s, v856) { Ok(v) => v, Err(e) => return Err(e) };
let v858 = match s.builtin_list(EvalOp::ListRev, &[v854, v857]) { Ok(v) => v, Err(e) => return Err(e) };
let v859 = match eo__24str_5fre_5fconsume_5frec(s, v847, v853, v858) { Ok(v) => v, Err(e) => return Err(e) };
let v860 = match eo__24str_5fmembership_5fstr(s, v859) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v860)
}
pub(super) fn if_53_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v838 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v839 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v840 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v839, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v841 = match eo__24str_5fflatten(s, v840) { Ok(v) => v, Err(e) => return Err(e) };
let v842 = match s.builtin_list(EvalOp::ListRev, &[v838, v841]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v842)
}
Some(false) => {
let v843 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v844 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v845 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v844, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v846 = match eo__24str_5fflatten(s, v845) { Ok(v) => v, Err(e) => return Err(e) };
let v847 = match s.builtin_list(EvalOp::ListRev, &[v843, v846]) { Ok(v) => v, Err(e) => return Err(e) };
let v848 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v849 = match eo__24re_5fflatten(s, v848, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v850 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v851 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v852 = match s.apply(v850, v851) { Ok(v) => v, Err(e) => return Err(e) };
let v853 = match eo__24re_5frev_5fmap_5frev(s, v849, v852) { Ok(v) => v, Err(e) => return Err(e) };
let v854 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_52_eo__24str_5fre_5fconsume(s, a0, v854, v847, v853)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_54_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v912: Term, v905: Term, v911: Term) -> CheckResult<Term> {
let v913 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v914 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v913, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v915 = match eo__24str_5fflatten(s, v914) { Ok(v) => v, Err(e) => return Err(e) };
let v916 = match s.builtin_list(EvalOp::ListRev, &[v912, v915]) { Ok(v) => v, Err(e) => return Err(e) };
let v917 = match eo__24str_5fre_5fconsume_5frec(s, v905, v911, v916) { Ok(v) => v, Err(e) => return Err(e) };
let v918 = match eo__24str_5fmembership_5fstr(s, v917) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v918)
}
pub(super) fn if_55_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v896 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v897 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v898 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v897, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v899 = match eo__24str_5fflatten(s, v898) { Ok(v) => v, Err(e) => return Err(e) };
let v900 = match s.builtin_list(EvalOp::ListRev, &[v896, v899]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v900)
}
Some(false) => {
let v901 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v902 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v903 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v902, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v904 = match eo__24str_5fflatten(s, v903) { Ok(v) => v, Err(e) => return Err(e) };
let v905 = match s.builtin_list(EvalOp::ListRev, &[v901, v904]) { Ok(v) => v, Err(e) => return Err(e) };
let v906 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v907 = match eo__24re_5fflatten(s, v906, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v908 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v909 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v910 = match s.apply(v908, v909) { Ok(v) => v, Err(e) => return Err(e) };
let v911 = match eo__24re_5frev_5fmap_5frev(s, v907, v910) { Ok(v) => v, Err(e) => return Err(e) };
let v912 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_54_eo__24str_5fre_5fconsume(s, a0, v912, v905, v911)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_56_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v964: Term, v957: Term, v963: Term) -> CheckResult<Term> {
let v965 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v966 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v965, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v967 = match eo__24str_5fflatten(s, v966) { Ok(v) => v, Err(e) => return Err(e) };
let v968 = match s.builtin_list(EvalOp::ListRev, &[v964, v967]) { Ok(v) => v, Err(e) => return Err(e) };
let v969 = match eo__24str_5fre_5fconsume_5frec(s, v957, v963, v968) { Ok(v) => v, Err(e) => return Err(e) };
let v970 = match eo__24str_5fmembership_5fre(s, v969) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v970)
}
pub(super) fn if_57_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v947 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v948 = match eo__24re_5fflatten(s, v947, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v949 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v950 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v951 = match s.apply(v949, v950) { Ok(v) => v, Err(e) => return Err(e) };
let v952 = match eo__24re_5frev_5fmap_5frev(s, v948, v951) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v952)
}
Some(false) => {
let v953 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v954 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v955 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v954, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v956 = match eo__24str_5fflatten(s, v955) { Ok(v) => v, Err(e) => return Err(e) };
let v957 = match s.builtin_list(EvalOp::ListRev, &[v953, v956]) { Ok(v) => v, Err(e) => return Err(e) };
let v958 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v959 = match eo__24re_5fflatten(s, v958, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v960 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v961 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v962 = match s.apply(v960, v961) { Ok(v) => v, Err(e) => return Err(e) };
let v963 = match eo__24re_5frev_5fmap_5frev(s, v959, v962) { Ok(v) => v, Err(e) => return Err(e) };
let v964 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_56_eo__24str_5fre_5fconsume(s, a0, v964, v957, v963)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_58_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1019: Term, v1012: Term, v1018: Term) -> CheckResult<Term> {
let v1020 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1021 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1020, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1022 = match eo__24str_5fflatten(s, v1021) { Ok(v) => v, Err(e) => return Err(e) };
let v1023 = match s.builtin_list(EvalOp::ListRev, &[v1019, v1022]) { Ok(v) => v, Err(e) => return Err(e) };
let v1024 = match eo__24str_5fre_5fconsume_5frec(s, v1012, v1018, v1023) { Ok(v) => v, Err(e) => return Err(e) };
let v1025 = match eo__24str_5fmembership_5fstr(s, v1024) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1025)
}
pub(super) fn if_59_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1003 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1004 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1005 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1004, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1006 = match eo__24str_5fflatten(s, v1005) { Ok(v) => v, Err(e) => return Err(e) };
let v1007 = match s.builtin_list(EvalOp::ListRev, &[v1003, v1006]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1007)
}
Some(false) => {
let v1008 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1009 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1010 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1009, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1011 = match eo__24str_5fflatten(s, v1010) { Ok(v) => v, Err(e) => return Err(e) };
let v1012 = match s.builtin_list(EvalOp::ListRev, &[v1008, v1011]) { Ok(v) => v, Err(e) => return Err(e) };
let v1013 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1014 = match eo__24re_5fflatten(s, v1013, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1015 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1016 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1017 = match s.apply(v1015, v1016) { Ok(v) => v, Err(e) => return Err(e) };
let v1018 = match eo__24re_5frev_5fmap_5frev(s, v1014, v1017) { Ok(v) => v, Err(e) => return Err(e) };
let v1019 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_58_eo__24str_5fre_5fconsume(s, a0, v1019, v1012, v1018)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_74_eo__24str_5fre_5fconsume(s: &mut Store, v996: Term, v999: Term, v978: Term, a0: Term, v2: Term, v977: Term, v920: Term, v976: Term, v869: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v1000 = match s.builtin_core(EvalOp::Eq, &[v996, v999]) { Ok(v) => v, Err(e) => return Err(e) };
let v1001 = match s.builtin_core(EvalOp::Not, &[v1000]) { Ok(v) => v, Err(e) => return Err(e) };
let v1002 = match s.builtin_core(EvalOp::And, &[v978, v1001]) { Ok(v) => v, Err(e) => return Err(e) };
let v1026 = match if_59_eo__24str_5fre_5fconsume(s, v1002, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1027 = match s.builtin_list(EvalOp::ListRev, &[v977, v1026]) { Ok(v) => v, Err(e) => return Err(e) };
let v1028 = match eo__24str_5fre_5fconsume_5frec(s, v920, v976, v1027) { Ok(v) => v, Err(e) => return Err(e) };
let v1029 = match eo__24str_5fmembership_5fre(s, v1028) { Ok(v) => v, Err(e) => return Err(e) };
let v1030 = match eo__24re_5funflatten(s, v869, v1029) { Ok(v) => v, Err(e) => return Err(e) };
let v1031 = match s.builtin_list(EvalOp::ListSingletonElim, &[v868, v1030]) { Ok(v) => v, Err(e) => return Err(e) };
let v1032 = match s.apply(v867, v1031) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1032)
}
pub(super) fn more_73_eo__24str_5fre_5fconsume(s: &mut Store, v986: Term, v987: Term, v985: Term, a0: Term, v983: Term, v978: Term, v2: Term, v977: Term, v920: Term, v976: Term, v869: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v988 = match s.apply(v986, v987) { Ok(v) => v, Err(e) => return Err(e) };
let v989 = match eo__24re_5frev_5fmap_5frev(s, v985, v988) { Ok(v) => v, Err(e) => return Err(e) };
let v990 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v991 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v992 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v991, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v993 = match eo__24str_5fflatten(s, v992) { Ok(v) => v, Err(e) => return Err(e) };
let v994 = match s.builtin_list(EvalOp::ListRev, &[v990, v993]) { Ok(v) => v, Err(e) => return Err(e) };
let v995 = match eo__24str_5fre_5fconsume_5frec(s, v983, v989, v994) { Ok(v) => v, Err(e) => return Err(e) };
let v996 = match eo__24str_5fmembership_5fre(s, v995) { Ok(v) => v, Err(e) => return Err(e) };
let v997 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v998 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v999 = match s.apply(v997, v998) { Ok(v) => v, Err(e) => return Err(e) };
more_74_eo__24str_5fre_5fconsume(s, v996, v999, v978, a0, v2, v977, v920, v976, v869, v868, v867)
}
pub(super) fn more_72_eo__24str_5fre_5fconsume(s: &mut Store, v972: Term, v975: Term, a0: Term, v2: Term, v920: Term, v869: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v976 = match eo__24re_5frev_5fmap_5frev(s, v972, v975) { Ok(v) => v, Err(e) => return Err(e) };
let v977 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v978 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v979 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v980 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v981 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v980, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v982 = match eo__24str_5fflatten(s, v981) { Ok(v) => v, Err(e) => return Err(e) };
let v983 = match s.builtin_list(EvalOp::ListRev, &[v979, v982]) { Ok(v) => v, Err(e) => return Err(e) };
let v984 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v985 = match eo__24re_5fflatten(s, v984, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v986 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v987 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_73_eo__24str_5fre_5fconsume(s, v986, v987, v985, a0, v983, v978, v2, v977, v920, v976, v869, v868, v867)
}
pub(super) fn more_71_eo__24str_5fre_5fconsume(s: &mut Store, v939: Term, v922: Term, v2: Term, a0: Term, v921: Term, v920: Term, v869: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v940 = match eo__24str_5fmembership_5fre(s, v939) { Ok(v) => v, Err(e) => return Err(e) };
let v941 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v942 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v943 = match s.apply(v941, v942) { Ok(v) => v, Err(e) => return Err(e) };
let v944 = match s.builtin_core(EvalOp::Eq, &[v940, v943]) { Ok(v) => v, Err(e) => return Err(e) };
let v945 = match s.builtin_core(EvalOp::Not, &[v944]) { Ok(v) => v, Err(e) => return Err(e) };
let v946 = match s.builtin_core(EvalOp::And, &[v922, v945]) { Ok(v) => v, Err(e) => return Err(e) };
let v971 = match if_57_eo__24str_5fre_5fconsume(s, v946, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v972 = match eo__24re_5fflatten(s, v921, v971) { Ok(v) => v, Err(e) => return Err(e) };
let v973 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v974 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v975 = match s.apply(v973, v974) { Ok(v) => v, Err(e) => return Err(e) };
more_72_eo__24str_5fre_5fconsume(s, v972, v975, a0, v2, v920, v869, v868, v867)
}
pub(super) fn more_70_eo__24str_5fre_5fconsume(s: &mut Store, v2: Term, a0: Term, v927: Term, v922: Term, v921: Term, v920: Term, v869: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v928 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v929 = match eo__24re_5fflatten(s, v928, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v930 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v931 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v932 = match s.apply(v930, v931) { Ok(v) => v, Err(e) => return Err(e) };
let v933 = match eo__24re_5frev_5fmap_5frev(s, v929, v932) { Ok(v) => v, Err(e) => return Err(e) };
let v934 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v935 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v936 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v935, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v937 = match eo__24str_5fflatten(s, v936) { Ok(v) => v, Err(e) => return Err(e) };
let v938 = match s.builtin_list(EvalOp::ListRev, &[v934, v937]) { Ok(v) => v, Err(e) => return Err(e) };
let v939 = match eo__24str_5fre_5fconsume_5frec(s, v927, v933, v938) { Ok(v) => v, Err(e) => return Err(e) };
more_71_eo__24str_5fre_5fconsume(s, v939, v922, v2, a0, v921, v920, v869, v868, v867)
}
pub(super) fn more_69_eo__24str_5fre_5fconsume(s: &mut Store, v889: Term, v892: Term, v871: Term, a0: Term, v2: Term, v870: Term, v869: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v893 = match s.builtin_core(EvalOp::Eq, &[v889, v892]) { Ok(v) => v, Err(e) => return Err(e) };
let v894 = match s.builtin_core(EvalOp::Not, &[v893]) { Ok(v) => v, Err(e) => return Err(e) };
let v895 = match s.builtin_core(EvalOp::And, &[v871, v894]) { Ok(v) => v, Err(e) => return Err(e) };
let v919 = match if_55_eo__24str_5fre_5fconsume(s, v895, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v920 = match s.builtin_list(EvalOp::ListRev, &[v870, v919]) { Ok(v) => v, Err(e) => return Err(e) };
let v921 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v922 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v923 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v924 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v925 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v924, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v926 = match eo__24str_5fflatten(s, v925) { Ok(v) => v, Err(e) => return Err(e) };
let v927 = match s.builtin_list(EvalOp::ListRev, &[v923, v926]) { Ok(v) => v, Err(e) => return Err(e) };
more_70_eo__24str_5fre_5fconsume(s, v2, a0, v927, v922, v921, v920, v869, v868, v867)
}
pub(super) fn more_68_eo__24str_5fre_5fconsume(s: &mut Store, v879: Term, v880: Term, v878: Term, a0: Term, v876: Term, v871: Term, v2: Term, v870: Term, v869: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v881 = match s.apply(v879, v880) { Ok(v) => v, Err(e) => return Err(e) };
let v882 = match eo__24re_5frev_5fmap_5frev(s, v878, v881) { Ok(v) => v, Err(e) => return Err(e) };
let v883 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v884 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v885 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v884, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v886 = match eo__24str_5fflatten(s, v885) { Ok(v) => v, Err(e) => return Err(e) };
let v887 = match s.builtin_list(EvalOp::ListRev, &[v883, v886]) { Ok(v) => v, Err(e) => return Err(e) };
let v888 = match eo__24str_5fre_5fconsume_5frec(s, v876, v882, v887) { Ok(v) => v, Err(e) => return Err(e) };
let v889 = match eo__24str_5fmembership_5fre(s, v888) { Ok(v) => v, Err(e) => return Err(e) };
let v890 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v891 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v892 = match s.apply(v890, v891) { Ok(v) => v, Err(e) => return Err(e) };
more_69_eo__24str_5fre_5fconsume(s, v889, v892, v871, a0, v2, v870, v869, v868, v867)
}
pub(super) fn more_67_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v2: Term, v868: Term, v867: Term) -> CheckResult<Term> {
let v869 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v870 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v871 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v872 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v873 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v874 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v873, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v875 = match eo__24str_5fflatten(s, v874) { Ok(v) => v, Err(e) => return Err(e) };
let v876 = match s.builtin_list(EvalOp::ListRev, &[v872, v875]) { Ok(v) => v, Err(e) => return Err(e) };
let v877 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v878 = match eo__24re_5fflatten(s, v877, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v879 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v880 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_68_eo__24str_5fre_5fconsume(s, v879, v880, v878, a0, v876, v871, v2, v870, v869, v868, v867)
}
pub(super) fn more_66_eo__24str_5fre_5fconsume(s: &mut Store, v832: Term, v833: Term, v831: Term, v813: Term, a0: Term, v2: Term, v812: Term, v755: Term, v811: Term, v704: Term, v703: Term) -> CheckResult<Term> {
let v834 = match s.apply(v832, v833) { Ok(v) => v, Err(e) => return Err(e) };
let v835 = match s.builtin_core(EvalOp::Eq, &[v831, v834]) { Ok(v) => v, Err(e) => return Err(e) };
let v836 = match s.builtin_core(EvalOp::Not, &[v835]) { Ok(v) => v, Err(e) => return Err(e) };
let v837 = match s.builtin_core(EvalOp::And, &[v813, v836]) { Ok(v) => v, Err(e) => return Err(e) };
let v861 = match if_53_eo__24str_5fre_5fconsume(s, v837, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v862 = match s.builtin_list(EvalOp::ListRev, &[v812, v861]) { Ok(v) => v, Err(e) => return Err(e) };
let v863 = match eo__24str_5fre_5fconsume_5frec(s, v755, v811, v862) { Ok(v) => v, Err(e) => return Err(e) };
let v864 = match eo__24str_5fmembership_5fstr(s, v863) { Ok(v) => v, Err(e) => return Err(e) };
let v865 = match eo__24str_5fcollect(s, v864) { Ok(v) => v, Err(e) => return Err(e) };
let v866 = match s.builtin_list(EvalOp::ListSingletonElim, &[v704, v865]) { Ok(v) => v, Err(e) => return Err(e) };
let v867 = match s.apply(v703, v866) { Ok(v) => v, Err(e) => return Err(e) };
let v868 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_67_eo__24str_5fre_5fconsume(s, a0, v2, v868, v867)
}
pub(super) fn more_65_eo__24str_5fre_5fconsume(s: &mut Store, v821: Term, v820: Term, a0: Term, v818: Term, v813: Term, v2: Term, v812: Term, v755: Term, v811: Term, v704: Term, v703: Term) -> CheckResult<Term> {
let v822 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v823 = match s.apply(v821, v822) { Ok(v) => v, Err(e) => return Err(e) };
let v824 = match eo__24re_5frev_5fmap_5frev(s, v820, v823) { Ok(v) => v, Err(e) => return Err(e) };
let v825 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v826 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v827 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v826, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v828 = match eo__24str_5fflatten(s, v827) { Ok(v) => v, Err(e) => return Err(e) };
let v829 = match s.builtin_list(EvalOp::ListRev, &[v825, v828]) { Ok(v) => v, Err(e) => return Err(e) };
let v830 = match eo__24str_5fre_5fconsume_5frec(s, v818, v824, v829) { Ok(v) => v, Err(e) => return Err(e) };
let v831 = match eo__24str_5fmembership_5fre(s, v830) { Ok(v) => v, Err(e) => return Err(e) };
let v832 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v833 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_66_eo__24str_5fre_5fconsume(s, v832, v833, v831, v813, a0, v2, v812, v755, v811, v704, v703)
}
pub(super) fn more_64_eo__24str_5fre_5fconsume(s: &mut Store, v808: Term, v809: Term, v807: Term, a0: Term, v2: Term, v755: Term, v704: Term, v703: Term) -> CheckResult<Term> {
let v810 = match s.apply(v808, v809) { Ok(v) => v, Err(e) => return Err(e) };
let v811 = match eo__24re_5frev_5fmap_5frev(s, v807, v810) { Ok(v) => v, Err(e) => return Err(e) };
let v812 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v813 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v814 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v815 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v816 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v815, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v817 = match eo__24str_5fflatten(s, v816) { Ok(v) => v, Err(e) => return Err(e) };
let v818 = match s.builtin_list(EvalOp::ListRev, &[v814, v817]) { Ok(v) => v, Err(e) => return Err(e) };
let v819 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v820 = match eo__24re_5fflatten(s, v819, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v821 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_65_eo__24str_5fre_5fconsume(s, v821, v820, a0, v818, v813, v2, v812, v755, v811, v704, v703)
}
pub(super) fn more_63_eo__24str_5fre_5fconsume(s: &mut Store, v762: Term, v768: Term, v773: Term, v757: Term, v2: Term, a0: Term, v756: Term, v755: Term, v704: Term, v703: Term) -> CheckResult<Term> {
let v774 = match eo__24str_5fre_5fconsume_5frec(s, v762, v768, v773) { Ok(v) => v, Err(e) => return Err(e) };
let v775 = match eo__24str_5fmembership_5fre(s, v774) { Ok(v) => v, Err(e) => return Err(e) };
let v776 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v777 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v778 = match s.apply(v776, v777) { Ok(v) => v, Err(e) => return Err(e) };
let v779 = match s.builtin_core(EvalOp::Eq, &[v775, v778]) { Ok(v) => v, Err(e) => return Err(e) };
let v780 = match s.builtin_core(EvalOp::Not, &[v779]) { Ok(v) => v, Err(e) => return Err(e) };
let v781 = match s.builtin_core(EvalOp::And, &[v757, v780]) { Ok(v) => v, Err(e) => return Err(e) };
let v806 = match if_51_eo__24str_5fre_5fconsume(s, v781, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v807 = match eo__24re_5fflatten(s, v756, v806) { Ok(v) => v, Err(e) => return Err(e) };
let v808 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v809 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_64_eo__24str_5fre_5fconsume(s, v808, v809, v807, a0, v2, v755, v704, v703)
}
pub(super) fn more_62_eo__24str_5fre_5fconsume(s: &mut Store, v758: Term, v761: Term, v2: Term, a0: Term, v757: Term, v756: Term, v755: Term, v704: Term, v703: Term) -> CheckResult<Term> {
let v762 = match s.builtin_list(EvalOp::ListRev, &[v758, v761]) { Ok(v) => v, Err(e) => return Err(e) };
let v763 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v764 = match eo__24re_5fflatten(s, v763, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v765 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v766 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v767 = match s.apply(v765, v766) { Ok(v) => v, Err(e) => return Err(e) };
let v768 = match eo__24re_5frev_5fmap_5frev(s, v764, v767) { Ok(v) => v, Err(e) => return Err(e) };
let v769 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v770 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v771 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v770, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v772 = match eo__24str_5fflatten(s, v771) { Ok(v) => v, Err(e) => return Err(e) };
let v773 = match s.builtin_list(EvalOp::ListRev, &[v769, v772]) { Ok(v) => v, Err(e) => return Err(e) };
more_63_eo__24str_5fre_5fconsume(s, v762, v768, v773, v757, v2, a0, v756, v755, v704, v703)
}
pub(super) fn more_61_eo__24str_5fre_5fconsume(s: &mut Store, v725: Term, v726: Term, v724: Term, v706: Term, a0: Term, v2: Term, v705: Term, v704: Term, v703: Term) -> CheckResult<Term> {
let v727 = match s.apply(v725, v726) { Ok(v) => v, Err(e) => return Err(e) };
let v728 = match s.builtin_core(EvalOp::Eq, &[v724, v727]) { Ok(v) => v, Err(e) => return Err(e) };
let v729 = match s.builtin_core(EvalOp::Not, &[v728]) { Ok(v) => v, Err(e) => return Err(e) };
let v730 = match s.builtin_core(EvalOp::And, &[v706, v729]) { Ok(v) => v, Err(e) => return Err(e) };
let v754 = match if_49_eo__24str_5fre_5fconsume(s, v730, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v755 = match s.builtin_list(EvalOp::ListRev, &[v705, v754]) { Ok(v) => v, Err(e) => return Err(e) };
let v756 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v757 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v758 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v759 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v760 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v759, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v761 = match eo__24str_5fflatten(s, v760) { Ok(v) => v, Err(e) => return Err(e) };
more_62_eo__24str_5fre_5fconsume(s, v758, v761, v2, a0, v757, v756, v755, v704, v703)
}
pub(super) fn more_60_eo__24str_5fre_5fconsume(s: &mut Store, v714: Term, v713: Term, a0: Term, v711: Term, v706: Term, v2: Term, v705: Term, v704: Term, v703: Term) -> CheckResult<Term> {
let v715 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v716 = match s.apply(v714, v715) { Ok(v) => v, Err(e) => return Err(e) };
let v717 = match eo__24re_5frev_5fmap_5frev(s, v713, v716) { Ok(v) => v, Err(e) => return Err(e) };
let v718 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v719 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v720 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v719, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v721 = match eo__24str_5fflatten(s, v720) { Ok(v) => v, Err(e) => return Err(e) };
let v722 = match s.builtin_list(EvalOp::ListRev, &[v718, v721]) { Ok(v) => v, Err(e) => return Err(e) };
let v723 = match eo__24str_5fre_5fconsume_5frec(s, v711, v717, v722) { Ok(v) => v, Err(e) => return Err(e) };
let v724 = match eo__24str_5fmembership_5fre(s, v723) { Ok(v) => v, Err(e) => return Err(e) };
let v725 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v726 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_61_eo__24str_5fre_5fconsume(s, v725, v726, v724, v706, a0, v2, v705, v704, v703)
}
pub(super) fn if_75_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v702 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v702)
}
Some(false) => {
let v703 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v704 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v705 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v706 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v707 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v708 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v709 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v708, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v710 = match eo__24str_5fflatten(s, v709) { Ok(v) => v, Err(e) => return Err(e) };
let v711 = match s.builtin_list(EvalOp::ListRev, &[v707, v710]) { Ok(v) => v, Err(e) => return Err(e) };
let v712 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v713 = match eo__24re_5fflatten(s, v712, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v714 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_60_eo__24str_5fre_5fconsume(s, v714, v713, a0, v711, v706, v2, v705, v704, v703)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_82_eo__24str_5fre_5fconsume(s: &mut Store, v671: Term, v649: Term, a0: Term, v2: Term, v648: Term, v591: Term, v647: Term) -> CheckResult<Term> {
let v672 = match s.builtin_core(EvalOp::Not, &[v671]) { Ok(v) => v, Err(e) => return Err(e) };
let v673 = match s.builtin_core(EvalOp::And, &[v649, v672]) { Ok(v) => v, Err(e) => return Err(e) };
let v697 = match if_47_eo__24str_5fre_5fconsume(s, v673, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v698 = match s.builtin_list(EvalOp::ListRev, &[v648, v697]) { Ok(v) => v, Err(e) => return Err(e) };
let v699 = match eo__24str_5fre_5fconsume_5frec(s, v591, v647, v698) { Ok(v) => v, Err(e) => return Err(e) };
let v700 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v701 = match s.builtin_core(EvalOp::Eq, &[v699, v700]) { Ok(v) => v, Err(e) => return Err(e) };
let v1033 = match if_75_eo__24str_5fre_5fconsume(s, v701, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1033)
}
pub(super) fn more_81_eo__24str_5fre_5fconsume(s: &mut Store, v656: Term, v659: Term, a0: Term, v654: Term, v649: Term, v2: Term, v648: Term, v591: Term, v647: Term) -> CheckResult<Term> {
let v660 = match eo__24re_5frev_5fmap_5frev(s, v656, v659) { Ok(v) => v, Err(e) => return Err(e) };
let v661 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v662 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v663 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v662, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v664 = match eo__24str_5fflatten(s, v663) { Ok(v) => v, Err(e) => return Err(e) };
let v665 = match s.builtin_list(EvalOp::ListRev, &[v661, v664]) { Ok(v) => v, Err(e) => return Err(e) };
let v666 = match eo__24str_5fre_5fconsume_5frec(s, v654, v660, v665) { Ok(v) => v, Err(e) => return Err(e) };
let v667 = match eo__24str_5fmembership_5fre(s, v666) { Ok(v) => v, Err(e) => return Err(e) };
let v668 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v669 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v670 = match s.apply(v668, v669) { Ok(v) => v, Err(e) => return Err(e) };
let v671 = match s.builtin_core(EvalOp::Eq, &[v667, v670]) { Ok(v) => v, Err(e) => return Err(e) };
more_82_eo__24str_5fre_5fconsume(s, v671, v649, a0, v2, v648, v591, v647)
}
pub(super) fn more_80_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v2: Term, v591: Term, v647: Term) -> CheckResult<Term> {
let v648 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v649 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v650 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v651 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v652 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v651, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v653 = match eo__24str_5fflatten(s, v652) { Ok(v) => v, Err(e) => return Err(e) };
let v654 = match s.builtin_list(EvalOp::ListRev, &[v650, v653]) { Ok(v) => v, Err(e) => return Err(e) };
let v655 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v656 = match eo__24re_5fflatten(s, v655, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v657 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v658 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v659 = match s.apply(v657, v658) { Ok(v) => v, Err(e) => return Err(e) };
more_81_eo__24str_5fre_5fconsume(s, v656, v659, a0, v654, v649, v2, v648, v591, v647)
}
pub(super) fn more_79_eo__24str_5fre_5fconsume(s: &mut Store, v611: Term, v593: Term, v2: Term, a0: Term, v592: Term, v591: Term) -> CheckResult<Term> {
let v612 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v613 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v614 = match s.apply(v612, v613) { Ok(v) => v, Err(e) => return Err(e) };
let v615 = match s.builtin_core(EvalOp::Eq, &[v611, v614]) { Ok(v) => v, Err(e) => return Err(e) };
let v616 = match s.builtin_core(EvalOp::Not, &[v615]) { Ok(v) => v, Err(e) => return Err(e) };
let v617 = match s.builtin_core(EvalOp::And, &[v593, v616]) { Ok(v) => v, Err(e) => return Err(e) };
let v642 = match if_45_eo__24str_5fre_5fconsume(s, v617, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v643 = match eo__24re_5fflatten(s, v592, v642) { Ok(v) => v, Err(e) => return Err(e) };
let v644 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v645 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v646 = match s.apply(v644, v645) { Ok(v) => v, Err(e) => return Err(e) };
let v647 = match eo__24re_5frev_5fmap_5frev(s, v643, v646) { Ok(v) => v, Err(e) => return Err(e) };
more_80_eo__24str_5fre_5fconsume(s, a0, v2, v591, v647)
}
pub(super) fn more_78_eo__24str_5fre_5fconsume(s: &mut Store, v599: Term, v2: Term, a0: Term, v598: Term, v593: Term, v592: Term, v591: Term) -> CheckResult<Term> {
let v600 = match eo__24re_5fflatten(s, v599, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v601 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v602 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v603 = match s.apply(v601, v602) { Ok(v) => v, Err(e) => return Err(e) };
let v604 = match eo__24re_5frev_5fmap_5frev(s, v600, v603) { Ok(v) => v, Err(e) => return Err(e) };
let v605 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v606 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v607 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v606, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v608 = match eo__24str_5fflatten(s, v607) { Ok(v) => v, Err(e) => return Err(e) };
let v609 = match s.builtin_list(EvalOp::ListRev, &[v605, v608]) { Ok(v) => v, Err(e) => return Err(e) };
let v610 = match eo__24str_5fre_5fconsume_5frec(s, v598, v604, v609) { Ok(v) => v, Err(e) => return Err(e) };
let v611 = match eo__24str_5fmembership_5fre(s, v610) { Ok(v) => v, Err(e) => return Err(e) };
more_79_eo__24str_5fre_5fconsume(s, v611, v593, v2, a0, v592, v591)
}
pub(super) fn more_77_eo__24str_5fre_5fconsume(s: &mut Store, v564: Term, v542: Term, a0: Term, v2: Term, v541: Term) -> CheckResult<Term> {
let v565 = match s.builtin_core(EvalOp::Not, &[v564]) { Ok(v) => v, Err(e) => return Err(e) };
let v566 = match s.builtin_core(EvalOp::And, &[v542, v565]) { Ok(v) => v, Err(e) => return Err(e) };
let v590 = match if_43_eo__24str_5fre_5fconsume(s, v566, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v591 = match s.builtin_list(EvalOp::ListRev, &[v541, v590]) { Ok(v) => v, Err(e) => return Err(e) };
let v592 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v593 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v594 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v595 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v596 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v595, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v597 = match eo__24str_5fflatten(s, v596) { Ok(v) => v, Err(e) => return Err(e) };
let v598 = match s.builtin_list(EvalOp::ListRev, &[v594, v597]) { Ok(v) => v, Err(e) => return Err(e) };
let v599 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_78_eo__24str_5fre_5fconsume(s, v599, v2, a0, v598, v593, v592, v591)
}
pub(super) fn more_76_eo__24str_5fre_5fconsume(s: &mut Store, v549: Term, v552: Term, a0: Term, v547: Term, v542: Term, v2: Term, v541: Term) -> CheckResult<Term> {
let v553 = match eo__24re_5frev_5fmap_5frev(s, v549, v552) { Ok(v) => v, Err(e) => return Err(e) };
let v554 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v555 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v556 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v555, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v557 = match eo__24str_5fflatten(s, v556) { Ok(v) => v, Err(e) => return Err(e) };
let v558 = match s.builtin_list(EvalOp::ListRev, &[v554, v557]) { Ok(v) => v, Err(e) => return Err(e) };
let v559 = match eo__24str_5fre_5fconsume_5frec(s, v547, v553, v558) { Ok(v) => v, Err(e) => return Err(e) };
let v560 = match eo__24str_5fmembership_5fre(s, v559) { Ok(v) => v, Err(e) => return Err(e) };
let v561 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v562 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v563 = match s.apply(v561, v562) { Ok(v) => v, Err(e) => return Err(e) };
let v564 = match s.builtin_core(EvalOp::Eq, &[v560, v563]) { Ok(v) => v, Err(e) => return Err(e) };
more_77_eo__24str_5fre_5fconsume(s, v564, v542, a0, v2, v541)
}
pub(super) fn if_83_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v540 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v540)
}
Some(false) => {
let v541 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v542 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v543 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v544 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v545 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v544, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v546 = match eo__24str_5fflatten(s, v545) { Ok(v) => v, Err(e) => return Err(e) };
let v547 = match s.builtin_list(EvalOp::ListRev, &[v543, v546]) { Ok(v) => v, Err(e) => return Err(e) };
let v548 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v549 = match eo__24re_5fflatten(s, v548, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v550 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v551 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v552 = match s.apply(v550, v551) { Ok(v) => v, Err(e) => return Err(e) };
more_76_eo__24str_5fre_5fconsume(s, v549, v552, a0, v547, v542, v2, v541)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_84_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1102: Term, v1095: Term, v1101: Term) -> CheckResult<Term> {
let v1103 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1104 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1103, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1105 = match eo__24str_5fflatten(s, v1104) { Ok(v) => v, Err(e) => return Err(e) };
let v1106 = match s.builtin_list(EvalOp::ListRev, &[v1102, v1105]) { Ok(v) => v, Err(e) => return Err(e) };
let v1107 = match eo__24str_5fre_5fconsume_5frec(s, v1095, v1101, v1106) { Ok(v) => v, Err(e) => return Err(e) };
let v1108 = match eo__24str_5fmembership_5fstr(s, v1107) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1108)
}
pub(super) fn if_85_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1086 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1087 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1088 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1087, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1089 = match eo__24str_5fflatten(s, v1088) { Ok(v) => v, Err(e) => return Err(e) };
let v1090 = match s.builtin_list(EvalOp::ListRev, &[v1086, v1089]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1090)
}
Some(false) => {
let v1091 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1092 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1093 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1092, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1094 = match eo__24str_5fflatten(s, v1093) { Ok(v) => v, Err(e) => return Err(e) };
let v1095 = match s.builtin_list(EvalOp::ListRev, &[v1091, v1094]) { Ok(v) => v, Err(e) => return Err(e) };
let v1096 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1097 = match eo__24re_5fflatten(s, v1096, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1098 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1099 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1100 = match s.apply(v1098, v1099) { Ok(v) => v, Err(e) => return Err(e) };
let v1101 = match eo__24re_5frev_5fmap_5frev(s, v1097, v1100) { Ok(v) => v, Err(e) => return Err(e) };
let v1102 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_84_eo__24str_5fre_5fconsume(s, a0, v1102, v1095, v1101)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_86_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1154: Term, v1147: Term, v1153: Term) -> CheckResult<Term> {
let v1155 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1156 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1155, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1157 = match eo__24str_5fflatten(s, v1156) { Ok(v) => v, Err(e) => return Err(e) };
let v1158 = match s.builtin_list(EvalOp::ListRev, &[v1154, v1157]) { Ok(v) => v, Err(e) => return Err(e) };
let v1159 = match eo__24str_5fre_5fconsume_5frec(s, v1147, v1153, v1158) { Ok(v) => v, Err(e) => return Err(e) };
let v1160 = match eo__24str_5fmembership_5fre(s, v1159) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1160)
}
pub(super) fn if_87_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1137 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1138 = match eo__24re_5fflatten(s, v1137, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1139 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1140 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1141 = match s.apply(v1139, v1140) { Ok(v) => v, Err(e) => return Err(e) };
let v1142 = match eo__24re_5frev_5fmap_5frev(s, v1138, v1141) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1142)
}
Some(false) => {
let v1143 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1144 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1145 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1144, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1146 = match eo__24str_5fflatten(s, v1145) { Ok(v) => v, Err(e) => return Err(e) };
let v1147 = match s.builtin_list(EvalOp::ListRev, &[v1143, v1146]) { Ok(v) => v, Err(e) => return Err(e) };
let v1148 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1149 = match eo__24re_5fflatten(s, v1148, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1150 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1151 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1152 = match s.apply(v1150, v1151) { Ok(v) => v, Err(e) => return Err(e) };
let v1153 = match eo__24re_5frev_5fmap_5frev(s, v1149, v1152) { Ok(v) => v, Err(e) => return Err(e) };
let v1154 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_86_eo__24str_5fre_5fconsume(s, a0, v1154, v1147, v1153)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_88_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1209: Term, v1202: Term, v1208: Term) -> CheckResult<Term> {
let v1210 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1211 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1210, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1212 = match eo__24str_5fflatten(s, v1211) { Ok(v) => v, Err(e) => return Err(e) };
let v1213 = match s.builtin_list(EvalOp::ListRev, &[v1209, v1212]) { Ok(v) => v, Err(e) => return Err(e) };
let v1214 = match eo__24str_5fre_5fconsume_5frec(s, v1202, v1208, v1213) { Ok(v) => v, Err(e) => return Err(e) };
let v1215 = match eo__24str_5fmembership_5fstr(s, v1214) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1215)
}
pub(super) fn if_89_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1193 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1194 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1195 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1194, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1196 = match eo__24str_5fflatten(s, v1195) { Ok(v) => v, Err(e) => return Err(e) };
let v1197 = match s.builtin_list(EvalOp::ListRev, &[v1193, v1196]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1197)
}
Some(false) => {
let v1198 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1199 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1200 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1199, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1201 = match eo__24str_5fflatten(s, v1200) { Ok(v) => v, Err(e) => return Err(e) };
let v1202 = match s.builtin_list(EvalOp::ListRev, &[v1198, v1201]) { Ok(v) => v, Err(e) => return Err(e) };
let v1203 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1204 = match eo__24re_5fflatten(s, v1203, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1205 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1206 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1207 = match s.apply(v1205, v1206) { Ok(v) => v, Err(e) => return Err(e) };
let v1208 = match eo__24re_5frev_5fmap_5frev(s, v1204, v1207) { Ok(v) => v, Err(e) => return Err(e) };
let v1209 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_88_eo__24str_5fre_5fconsume(s, a0, v1209, v1202, v1208)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_90_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1266: Term, v1259: Term, v1265: Term) -> CheckResult<Term> {
let v1267 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1268 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1267, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1269 = match eo__24str_5fflatten(s, v1268) { Ok(v) => v, Err(e) => return Err(e) };
let v1270 = match s.builtin_list(EvalOp::ListRev, &[v1266, v1269]) { Ok(v) => v, Err(e) => return Err(e) };
let v1271 = match eo__24str_5fre_5fconsume_5frec(s, v1259, v1265, v1270) { Ok(v) => v, Err(e) => return Err(e) };
let v1272 = match eo__24str_5fmembership_5fstr(s, v1271) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1272)
}
pub(super) fn if_91_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1250 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1251 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1252 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1251, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1253 = match eo__24str_5fflatten(s, v1252) { Ok(v) => v, Err(e) => return Err(e) };
let v1254 = match s.builtin_list(EvalOp::ListRev, &[v1250, v1253]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1254)
}
Some(false) => {
let v1255 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1256 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1257 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1256, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1258 = match eo__24str_5fflatten(s, v1257) { Ok(v) => v, Err(e) => return Err(e) };
let v1259 = match s.builtin_list(EvalOp::ListRev, &[v1255, v1258]) { Ok(v) => v, Err(e) => return Err(e) };
let v1260 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1261 = match eo__24re_5fflatten(s, v1260, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1262 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1263 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1264 = match s.apply(v1262, v1263) { Ok(v) => v, Err(e) => return Err(e) };
let v1265 = match eo__24re_5frev_5fmap_5frev(s, v1261, v1264) { Ok(v) => v, Err(e) => return Err(e) };
let v1266 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_90_eo__24str_5fre_5fconsume(s, a0, v1266, v1259, v1265)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_92_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1318: Term, v1311: Term, v1317: Term) -> CheckResult<Term> {
let v1319 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1320 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1319, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1321 = match eo__24str_5fflatten(s, v1320) { Ok(v) => v, Err(e) => return Err(e) };
let v1322 = match s.builtin_list(EvalOp::ListRev, &[v1318, v1321]) { Ok(v) => v, Err(e) => return Err(e) };
let v1323 = match eo__24str_5fre_5fconsume_5frec(s, v1311, v1317, v1322) { Ok(v) => v, Err(e) => return Err(e) };
let v1324 = match eo__24str_5fmembership_5fre(s, v1323) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1324)
}
pub(super) fn if_93_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1301 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1302 = match eo__24re_5fflatten(s, v1301, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1303 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1304 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1305 = match s.apply(v1303, v1304) { Ok(v) => v, Err(e) => return Err(e) };
let v1306 = match eo__24re_5frev_5fmap_5frev(s, v1302, v1305) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1306)
}
Some(false) => {
let v1307 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1308 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1309 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1308, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1310 = match eo__24str_5fflatten(s, v1309) { Ok(v) => v, Err(e) => return Err(e) };
let v1311 = match s.builtin_list(EvalOp::ListRev, &[v1307, v1310]) { Ok(v) => v, Err(e) => return Err(e) };
let v1312 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1313 = match eo__24re_5fflatten(s, v1312, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1314 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1315 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1316 = match s.apply(v1314, v1315) { Ok(v) => v, Err(e) => return Err(e) };
let v1317 = match eo__24re_5frev_5fmap_5frev(s, v1313, v1316) { Ok(v) => v, Err(e) => return Err(e) };
let v1318 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_92_eo__24str_5fre_5fconsume(s, a0, v1318, v1311, v1317)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_94_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1373: Term, v1366: Term, v1372: Term) -> CheckResult<Term> {
let v1374 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1375 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1374, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1376 = match eo__24str_5fflatten(s, v1375) { Ok(v) => v, Err(e) => return Err(e) };
let v1377 = match s.builtin_list(EvalOp::ListRev, &[v1373, v1376]) { Ok(v) => v, Err(e) => return Err(e) };
let v1378 = match eo__24str_5fre_5fconsume_5frec(s, v1366, v1372, v1377) { Ok(v) => v, Err(e) => return Err(e) };
let v1379 = match eo__24str_5fmembership_5fstr(s, v1378) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1379)
}
pub(super) fn if_95_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1357 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1358 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1359 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1358, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1360 = match eo__24str_5fflatten(s, v1359) { Ok(v) => v, Err(e) => return Err(e) };
let v1361 = match s.builtin_list(EvalOp::ListRev, &[v1357, v1360]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1361)
}
Some(false) => {
let v1362 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1363 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1364 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1363, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1365 = match eo__24str_5fflatten(s, v1364) { Ok(v) => v, Err(e) => return Err(e) };
let v1366 = match s.builtin_list(EvalOp::ListRev, &[v1362, v1365]) { Ok(v) => v, Err(e) => return Err(e) };
let v1367 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1368 = match eo__24re_5fflatten(s, v1367, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1369 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1370 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1371 = match s.apply(v1369, v1370) { Ok(v) => v, Err(e) => return Err(e) };
let v1372 = match eo__24re_5frev_5fmap_5frev(s, v1368, v1371) { Ok(v) => v, Err(e) => return Err(e) };
let v1373 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_94_eo__24str_5fre_5fconsume(s, a0, v1373, v1366, v1372)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_96_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1431: Term, v1424: Term, v1430: Term) -> CheckResult<Term> {
let v1432 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1433 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1432, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1434 = match eo__24str_5fflatten(s, v1433) { Ok(v) => v, Err(e) => return Err(e) };
let v1435 = match s.builtin_list(EvalOp::ListRev, &[v1431, v1434]) { Ok(v) => v, Err(e) => return Err(e) };
let v1436 = match eo__24str_5fre_5fconsume_5frec(s, v1424, v1430, v1435) { Ok(v) => v, Err(e) => return Err(e) };
let v1437 = match eo__24str_5fmembership_5fstr(s, v1436) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1437)
}
pub(super) fn if_97_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1415 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1416 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1417 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1416, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1418 = match eo__24str_5fflatten(s, v1417) { Ok(v) => v, Err(e) => return Err(e) };
let v1419 = match s.builtin_list(EvalOp::ListRev, &[v1415, v1418]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1419)
}
Some(false) => {
let v1420 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1421 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1422 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1421, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1423 = match eo__24str_5fflatten(s, v1422) { Ok(v) => v, Err(e) => return Err(e) };
let v1424 = match s.builtin_list(EvalOp::ListRev, &[v1420, v1423]) { Ok(v) => v, Err(e) => return Err(e) };
let v1425 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1426 = match eo__24re_5fflatten(s, v1425, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1427 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1428 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1429 = match s.apply(v1427, v1428) { Ok(v) => v, Err(e) => return Err(e) };
let v1430 = match eo__24re_5frev_5fmap_5frev(s, v1426, v1429) { Ok(v) => v, Err(e) => return Err(e) };
let v1431 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_96_eo__24str_5fre_5fconsume(s, a0, v1431, v1424, v1430)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_98_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1483: Term, v1476: Term, v1482: Term) -> CheckResult<Term> {
let v1484 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1485 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1484, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1486 = match eo__24str_5fflatten(s, v1485) { Ok(v) => v, Err(e) => return Err(e) };
let v1487 = match s.builtin_list(EvalOp::ListRev, &[v1483, v1486]) { Ok(v) => v, Err(e) => return Err(e) };
let v1488 = match eo__24str_5fre_5fconsume_5frec(s, v1476, v1482, v1487) { Ok(v) => v, Err(e) => return Err(e) };
let v1489 = match eo__24str_5fmembership_5fre(s, v1488) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1489)
}
pub(super) fn if_99_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, v2: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1466 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1467 = match eo__24re_5fflatten(s, v1466, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1468 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1469 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1470 = match s.apply(v1468, v1469) { Ok(v) => v, Err(e) => return Err(e) };
let v1471 = match eo__24re_5frev_5fmap_5frev(s, v1467, v1470) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1471)
}
Some(false) => {
let v1472 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1473 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1474 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1473, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1475 = match eo__24str_5fflatten(s, v1474) { Ok(v) => v, Err(e) => return Err(e) };
let v1476 = match s.builtin_list(EvalOp::ListRev, &[v1472, v1475]) { Ok(v) => v, Err(e) => return Err(e) };
let v1477 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1478 = match eo__24re_5fflatten(s, v1477, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1479 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1480 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1481 = match s.apply(v1479, v1480) { Ok(v) => v, Err(e) => return Err(e) };
let v1482 = match eo__24re_5frev_5fmap_5frev(s, v1478, v1481) { Ok(v) => v, Err(e) => return Err(e) };
let v1483 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_98_eo__24str_5fre_5fconsume(s, a0, v1483, v1476, v1482)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_100_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1538: Term, v1531: Term, v1537: Term) -> CheckResult<Term> {
let v1539 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1540 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1539, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1541 = match eo__24str_5fflatten(s, v1540) { Ok(v) => v, Err(e) => return Err(e) };
let v1542 = match s.builtin_list(EvalOp::ListRev, &[v1538, v1541]) { Ok(v) => v, Err(e) => return Err(e) };
let v1543 = match eo__24str_5fre_5fconsume_5frec(s, v1531, v1537, v1542) { Ok(v) => v, Err(e) => return Err(e) };
let v1544 = match eo__24str_5fmembership_5fstr(s, v1543) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1544)
}
pub(super) fn if_101_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1522 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1523 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1524 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1523, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1525 = match eo__24str_5fflatten(s, v1524) { Ok(v) => v, Err(e) => return Err(e) };
let v1526 = match s.builtin_list(EvalOp::ListRev, &[v1522, v1525]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1526)
}
Some(false) => {
let v1527 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1528 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1529 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1528, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1530 = match eo__24str_5fflatten(s, v1529) { Ok(v) => v, Err(e) => return Err(e) };
let v1531 = match s.builtin_list(EvalOp::ListRev, &[v1527, v1530]) { Ok(v) => v, Err(e) => return Err(e) };
let v1532 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1533 = match eo__24re_5fflatten(s, v1532, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1534 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1535 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1536 = match s.apply(v1534, v1535) { Ok(v) => v, Err(e) => return Err(e) };
let v1537 = match eo__24re_5frev_5fmap_5frev(s, v1533, v1536) { Ok(v) => v, Err(e) => return Err(e) };
let v1538 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_100_eo__24str_5fre_5fconsume(s, a0, v1538, v1531, v1537)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_116_eo__24str_5fre_5fconsume(s: &mut Store, v1515: Term, v1518: Term, v1497: Term, a0: Term, v2: Term, v1496: Term, v1439: Term, v1495: Term, v1388: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1519 = match s.builtin_core(EvalOp::Eq, &[v1515, v1518]) { Ok(v) => v, Err(e) => return Err(e) };
let v1520 = match s.builtin_core(EvalOp::Not, &[v1519]) { Ok(v) => v, Err(e) => return Err(e) };
let v1521 = match s.builtin_core(EvalOp::And, &[v1497, v1520]) { Ok(v) => v, Err(e) => return Err(e) };
let v1545 = match if_101_eo__24str_5fre_5fconsume(s, v1521, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1546 = match s.builtin_list(EvalOp::ListRev, &[v1496, v1545]) { Ok(v) => v, Err(e) => return Err(e) };
let v1547 = match eo__24str_5fre_5fconsume_5frec(s, v1439, v1495, v1546) { Ok(v) => v, Err(e) => return Err(e) };
let v1548 = match eo__24str_5fmembership_5fre(s, v1547) { Ok(v) => v, Err(e) => return Err(e) };
let v1549 = match eo__24re_5funflatten(s, v1388, v1548) { Ok(v) => v, Err(e) => return Err(e) };
let v1550 = match s.builtin_list(EvalOp::ListSingletonElim, &[v1387, v1549]) { Ok(v) => v, Err(e) => return Err(e) };
let v1551 = match s.apply(v1386, v1550) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1551)
}
pub(super) fn more_115_eo__24str_5fre_5fconsume(s: &mut Store, v1505: Term, v1506: Term, v1504: Term, a0: Term, v1502: Term, v1497: Term, v2: Term, v1496: Term, v1439: Term, v1495: Term, v1388: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1507 = match s.apply(v1505, v1506) { Ok(v) => v, Err(e) => return Err(e) };
let v1508 = match eo__24re_5frev_5fmap_5frev(s, v1504, v1507) { Ok(v) => v, Err(e) => return Err(e) };
let v1509 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1510 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1511 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1510, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1512 = match eo__24str_5fflatten(s, v1511) { Ok(v) => v, Err(e) => return Err(e) };
let v1513 = match s.builtin_list(EvalOp::ListRev, &[v1509, v1512]) { Ok(v) => v, Err(e) => return Err(e) };
let v1514 = match eo__24str_5fre_5fconsume_5frec(s, v1502, v1508, v1513) { Ok(v) => v, Err(e) => return Err(e) };
let v1515 = match eo__24str_5fmembership_5fre(s, v1514) { Ok(v) => v, Err(e) => return Err(e) };
let v1516 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1517 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1518 = match s.apply(v1516, v1517) { Ok(v) => v, Err(e) => return Err(e) };
more_116_eo__24str_5fre_5fconsume(s, v1515, v1518, v1497, a0, v2, v1496, v1439, v1495, v1388, v1387, v1386)
}
pub(super) fn more_114_eo__24str_5fre_5fconsume(s: &mut Store, v1491: Term, v1494: Term, a0: Term, v2: Term, v1439: Term, v1388: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1495 = match eo__24re_5frev_5fmap_5frev(s, v1491, v1494) { Ok(v) => v, Err(e) => return Err(e) };
let v1496 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1497 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1498 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1499 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1500 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1499, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1501 = match eo__24str_5fflatten(s, v1500) { Ok(v) => v, Err(e) => return Err(e) };
let v1502 = match s.builtin_list(EvalOp::ListRev, &[v1498, v1501]) { Ok(v) => v, Err(e) => return Err(e) };
let v1503 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1504 = match eo__24re_5fflatten(s, v1503, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1505 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1506 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_115_eo__24str_5fre_5fconsume(s, v1505, v1506, v1504, a0, v1502, v1497, v2, v1496, v1439, v1495, v1388, v1387, v1386)
}
pub(super) fn more_113_eo__24str_5fre_5fconsume(s: &mut Store, v1458: Term, v1441: Term, v2: Term, a0: Term, v1440: Term, v1439: Term, v1388: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1459 = match eo__24str_5fmembership_5fre(s, v1458) { Ok(v) => v, Err(e) => return Err(e) };
let v1460 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1461 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1462 = match s.apply(v1460, v1461) { Ok(v) => v, Err(e) => return Err(e) };
let v1463 = match s.builtin_core(EvalOp::Eq, &[v1459, v1462]) { Ok(v) => v, Err(e) => return Err(e) };
let v1464 = match s.builtin_core(EvalOp::Not, &[v1463]) { Ok(v) => v, Err(e) => return Err(e) };
let v1465 = match s.builtin_core(EvalOp::And, &[v1441, v1464]) { Ok(v) => v, Err(e) => return Err(e) };
let v1490 = match if_99_eo__24str_5fre_5fconsume(s, v1465, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1491 = match eo__24re_5fflatten(s, v1440, v1490) { Ok(v) => v, Err(e) => return Err(e) };
let v1492 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1493 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1494 = match s.apply(v1492, v1493) { Ok(v) => v, Err(e) => return Err(e) };
more_114_eo__24str_5fre_5fconsume(s, v1491, v1494, a0, v2, v1439, v1388, v1387, v1386)
}
pub(super) fn more_112_eo__24str_5fre_5fconsume(s: &mut Store, v2: Term, a0: Term, v1446: Term, v1441: Term, v1440: Term, v1439: Term, v1388: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1447 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1448 = match eo__24re_5fflatten(s, v1447, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1449 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1450 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1451 = match s.apply(v1449, v1450) { Ok(v) => v, Err(e) => return Err(e) };
let v1452 = match eo__24re_5frev_5fmap_5frev(s, v1448, v1451) { Ok(v) => v, Err(e) => return Err(e) };
let v1453 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1454 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1455 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1454, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1456 = match eo__24str_5fflatten(s, v1455) { Ok(v) => v, Err(e) => return Err(e) };
let v1457 = match s.builtin_list(EvalOp::ListRev, &[v1453, v1456]) { Ok(v) => v, Err(e) => return Err(e) };
let v1458 = match eo__24str_5fre_5fconsume_5frec(s, v1446, v1452, v1457) { Ok(v) => v, Err(e) => return Err(e) };
more_113_eo__24str_5fre_5fconsume(s, v1458, v1441, v2, a0, v1440, v1439, v1388, v1387, v1386)
}
pub(super) fn more_111_eo__24str_5fre_5fconsume(s: &mut Store, v1408: Term, v1411: Term, v1390: Term, a0: Term, v2: Term, v1389: Term, v1388: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1412 = match s.builtin_core(EvalOp::Eq, &[v1408, v1411]) { Ok(v) => v, Err(e) => return Err(e) };
let v1413 = match s.builtin_core(EvalOp::Not, &[v1412]) { Ok(v) => v, Err(e) => return Err(e) };
let v1414 = match s.builtin_core(EvalOp::And, &[v1390, v1413]) { Ok(v) => v, Err(e) => return Err(e) };
let v1438 = match if_97_eo__24str_5fre_5fconsume(s, v1414, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1439 = match s.builtin_list(EvalOp::ListRev, &[v1389, v1438]) { Ok(v) => v, Err(e) => return Err(e) };
let v1440 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1441 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1442 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1443 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1444 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1443, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1445 = match eo__24str_5fflatten(s, v1444) { Ok(v) => v, Err(e) => return Err(e) };
let v1446 = match s.builtin_list(EvalOp::ListRev, &[v1442, v1445]) { Ok(v) => v, Err(e) => return Err(e) };
more_112_eo__24str_5fre_5fconsume(s, v2, a0, v1446, v1441, v1440, v1439, v1388, v1387, v1386)
}
pub(super) fn more_110_eo__24str_5fre_5fconsume(s: &mut Store, v1398: Term, v1399: Term, v1397: Term, a0: Term, v1395: Term, v1390: Term, v2: Term, v1389: Term, v1388: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1400 = match s.apply(v1398, v1399) { Ok(v) => v, Err(e) => return Err(e) };
let v1401 = match eo__24re_5frev_5fmap_5frev(s, v1397, v1400) { Ok(v) => v, Err(e) => return Err(e) };
let v1402 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1403 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1404 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1403, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1405 = match eo__24str_5fflatten(s, v1404) { Ok(v) => v, Err(e) => return Err(e) };
let v1406 = match s.builtin_list(EvalOp::ListRev, &[v1402, v1405]) { Ok(v) => v, Err(e) => return Err(e) };
let v1407 = match eo__24str_5fre_5fconsume_5frec(s, v1395, v1401, v1406) { Ok(v) => v, Err(e) => return Err(e) };
let v1408 = match eo__24str_5fmembership_5fre(s, v1407) { Ok(v) => v, Err(e) => return Err(e) };
let v1409 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1410 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1411 = match s.apply(v1409, v1410) { Ok(v) => v, Err(e) => return Err(e) };
more_111_eo__24str_5fre_5fconsume(s, v1408, v1411, v1390, a0, v2, v1389, v1388, v1387, v1386)
}
pub(super) fn more_109_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v2: Term, v1387: Term, v1386: Term) -> CheckResult<Term> {
let v1388 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1389 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1390 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1391 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1392 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1393 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1392, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1394 = match eo__24str_5fflatten(s, v1393) { Ok(v) => v, Err(e) => return Err(e) };
let v1395 = match s.builtin_list(EvalOp::ListRev, &[v1391, v1394]) { Ok(v) => v, Err(e) => return Err(e) };
let v1396 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1397 = match eo__24re_5fflatten(s, v1396, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1398 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1399 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_110_eo__24str_5fre_5fconsume(s, v1398, v1399, v1397, a0, v1395, v1390, v2, v1389, v1388, v1387, v1386)
}
pub(super) fn more_108_eo__24str_5fre_5fconsume(s: &mut Store, v1351: Term, v1352: Term, v1350: Term, v1332: Term, a0: Term, v2: Term, v1331: Term, v1274: Term, v1330: Term, v1223: Term, v1222: Term) -> CheckResult<Term> {
let v1353 = match s.apply(v1351, v1352) { Ok(v) => v, Err(e) => return Err(e) };
let v1354 = match s.builtin_core(EvalOp::Eq, &[v1350, v1353]) { Ok(v) => v, Err(e) => return Err(e) };
let v1355 = match s.builtin_core(EvalOp::Not, &[v1354]) { Ok(v) => v, Err(e) => return Err(e) };
let v1356 = match s.builtin_core(EvalOp::And, &[v1332, v1355]) { Ok(v) => v, Err(e) => return Err(e) };
let v1380 = match if_95_eo__24str_5fre_5fconsume(s, v1356, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1381 = match s.builtin_list(EvalOp::ListRev, &[v1331, v1380]) { Ok(v) => v, Err(e) => return Err(e) };
let v1382 = match eo__24str_5fre_5fconsume_5frec(s, v1274, v1330, v1381) { Ok(v) => v, Err(e) => return Err(e) };
let v1383 = match eo__24str_5fmembership_5fstr(s, v1382) { Ok(v) => v, Err(e) => return Err(e) };
let v1384 = match eo__24str_5fcollect(s, v1383) { Ok(v) => v, Err(e) => return Err(e) };
let v1385 = match s.builtin_list(EvalOp::ListSingletonElim, &[v1223, v1384]) { Ok(v) => v, Err(e) => return Err(e) };
let v1386 = match s.apply(v1222, v1385) { Ok(v) => v, Err(e) => return Err(e) };
let v1387 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_109_eo__24str_5fre_5fconsume(s, a0, v2, v1387, v1386)
}
pub(super) fn more_107_eo__24str_5fre_5fconsume(s: &mut Store, v1340: Term, v1339: Term, a0: Term, v1337: Term, v1332: Term, v2: Term, v1331: Term, v1274: Term, v1330: Term, v1223: Term, v1222: Term) -> CheckResult<Term> {
let v1341 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1342 = match s.apply(v1340, v1341) { Ok(v) => v, Err(e) => return Err(e) };
let v1343 = match eo__24re_5frev_5fmap_5frev(s, v1339, v1342) { Ok(v) => v, Err(e) => return Err(e) };
let v1344 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1345 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1346 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1345, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1347 = match eo__24str_5fflatten(s, v1346) { Ok(v) => v, Err(e) => return Err(e) };
let v1348 = match s.builtin_list(EvalOp::ListRev, &[v1344, v1347]) { Ok(v) => v, Err(e) => return Err(e) };
let v1349 = match eo__24str_5fre_5fconsume_5frec(s, v1337, v1343, v1348) { Ok(v) => v, Err(e) => return Err(e) };
let v1350 = match eo__24str_5fmembership_5fre(s, v1349) { Ok(v) => v, Err(e) => return Err(e) };
let v1351 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1352 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_108_eo__24str_5fre_5fconsume(s, v1351, v1352, v1350, v1332, a0, v2, v1331, v1274, v1330, v1223, v1222)
}
pub(super) fn more_106_eo__24str_5fre_5fconsume(s: &mut Store, v1327: Term, v1328: Term, v1326: Term, a0: Term, v2: Term, v1274: Term, v1223: Term, v1222: Term) -> CheckResult<Term> {
let v1329 = match s.apply(v1327, v1328) { Ok(v) => v, Err(e) => return Err(e) };
let v1330 = match eo__24re_5frev_5fmap_5frev(s, v1326, v1329) { Ok(v) => v, Err(e) => return Err(e) };
let v1331 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1332 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1333 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1334 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1335 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1334, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1336 = match eo__24str_5fflatten(s, v1335) { Ok(v) => v, Err(e) => return Err(e) };
let v1337 = match s.builtin_list(EvalOp::ListRev, &[v1333, v1336]) { Ok(v) => v, Err(e) => return Err(e) };
let v1338 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1339 = match eo__24re_5fflatten(s, v1338, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1340 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_107_eo__24str_5fre_5fconsume(s, v1340, v1339, a0, v1337, v1332, v2, v1331, v1274, v1330, v1223, v1222)
}
pub(super) fn more_105_eo__24str_5fre_5fconsume(s: &mut Store, v1281: Term, v1287: Term, v1292: Term, v1276: Term, v2: Term, a0: Term, v1275: Term, v1274: Term, v1223: Term, v1222: Term) -> CheckResult<Term> {
let v1293 = match eo__24str_5fre_5fconsume_5frec(s, v1281, v1287, v1292) { Ok(v) => v, Err(e) => return Err(e) };
let v1294 = match eo__24str_5fmembership_5fre(s, v1293) { Ok(v) => v, Err(e) => return Err(e) };
let v1295 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1296 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1297 = match s.apply(v1295, v1296) { Ok(v) => v, Err(e) => return Err(e) };
let v1298 = match s.builtin_core(EvalOp::Eq, &[v1294, v1297]) { Ok(v) => v, Err(e) => return Err(e) };
let v1299 = match s.builtin_core(EvalOp::Not, &[v1298]) { Ok(v) => v, Err(e) => return Err(e) };
let v1300 = match s.builtin_core(EvalOp::And, &[v1276, v1299]) { Ok(v) => v, Err(e) => return Err(e) };
let v1325 = match if_93_eo__24str_5fre_5fconsume(s, v1300, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1326 = match eo__24re_5fflatten(s, v1275, v1325) { Ok(v) => v, Err(e) => return Err(e) };
let v1327 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1328 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_106_eo__24str_5fre_5fconsume(s, v1327, v1328, v1326, a0, v2, v1274, v1223, v1222)
}
pub(super) fn more_104_eo__24str_5fre_5fconsume(s: &mut Store, v1277: Term, v1280: Term, v2: Term, a0: Term, v1276: Term, v1275: Term, v1274: Term, v1223: Term, v1222: Term) -> CheckResult<Term> {
let v1281 = match s.builtin_list(EvalOp::ListRev, &[v1277, v1280]) { Ok(v) => v, Err(e) => return Err(e) };
let v1282 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1283 = match eo__24re_5fflatten(s, v1282, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1284 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1285 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1286 = match s.apply(v1284, v1285) { Ok(v) => v, Err(e) => return Err(e) };
let v1287 = match eo__24re_5frev_5fmap_5frev(s, v1283, v1286) { Ok(v) => v, Err(e) => return Err(e) };
let v1288 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1289 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1290 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1289, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1291 = match eo__24str_5fflatten(s, v1290) { Ok(v) => v, Err(e) => return Err(e) };
let v1292 = match s.builtin_list(EvalOp::ListRev, &[v1288, v1291]) { Ok(v) => v, Err(e) => return Err(e) };
more_105_eo__24str_5fre_5fconsume(s, v1281, v1287, v1292, v1276, v2, a0, v1275, v1274, v1223, v1222)
}
pub(super) fn more_103_eo__24str_5fre_5fconsume(s: &mut Store, v1244: Term, v1245: Term, v1243: Term, v1225: Term, a0: Term, v2: Term, v1224: Term, v1223: Term, v1222: Term) -> CheckResult<Term> {
let v1246 = match s.apply(v1244, v1245) { Ok(v) => v, Err(e) => return Err(e) };
let v1247 = match s.builtin_core(EvalOp::Eq, &[v1243, v1246]) { Ok(v) => v, Err(e) => return Err(e) };
let v1248 = match s.builtin_core(EvalOp::Not, &[v1247]) { Ok(v) => v, Err(e) => return Err(e) };
let v1249 = match s.builtin_core(EvalOp::And, &[v1225, v1248]) { Ok(v) => v, Err(e) => return Err(e) };
let v1273 = match if_91_eo__24str_5fre_5fconsume(s, v1249, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1274 = match s.builtin_list(EvalOp::ListRev, &[v1224, v1273]) { Ok(v) => v, Err(e) => return Err(e) };
let v1275 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1276 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1277 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1278 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1279 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1278, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1280 = match eo__24str_5fflatten(s, v1279) { Ok(v) => v, Err(e) => return Err(e) };
more_104_eo__24str_5fre_5fconsume(s, v1277, v1280, v2, a0, v1276, v1275, v1274, v1223, v1222)
}
pub(super) fn more_102_eo__24str_5fre_5fconsume(s: &mut Store, v1233: Term, v1232: Term, a0: Term, v1230: Term, v1225: Term, v2: Term, v1224: Term, v1223: Term, v1222: Term) -> CheckResult<Term> {
let v1234 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1235 = match s.apply(v1233, v1234) { Ok(v) => v, Err(e) => return Err(e) };
let v1236 = match eo__24re_5frev_5fmap_5frev(s, v1232, v1235) { Ok(v) => v, Err(e) => return Err(e) };
let v1237 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1238 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1239 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1238, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1240 = match eo__24str_5fflatten(s, v1239) { Ok(v) => v, Err(e) => return Err(e) };
let v1241 = match s.builtin_list(EvalOp::ListRev, &[v1237, v1240]) { Ok(v) => v, Err(e) => return Err(e) };
let v1242 = match eo__24str_5fre_5fconsume_5frec(s, v1230, v1236, v1241) { Ok(v) => v, Err(e) => return Err(e) };
let v1243 = match eo__24str_5fmembership_5fre(s, v1242) { Ok(v) => v, Err(e) => return Err(e) };
let v1244 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1245 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_103_eo__24str_5fre_5fconsume(s, v1244, v1245, v1243, v1225, a0, v2, v1224, v1223, v1222)
}
pub(super) fn if_117_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1221 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1221)
}
Some(false) => {
let v1222 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1223 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1224 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1225 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1226 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1227 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1228 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1227, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1229 = match eo__24str_5fflatten(s, v1228) { Ok(v) => v, Err(e) => return Err(e) };
let v1230 = match s.builtin_list(EvalOp::ListRev, &[v1226, v1229]) { Ok(v) => v, Err(e) => return Err(e) };
let v1231 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1232 = match eo__24re_5fflatten(s, v1231, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1233 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_102_eo__24str_5fre_5fconsume(s, v1233, v1232, a0, v1230, v1225, v2, v1224, v1223, v1222)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_124_eo__24str_5fre_5fconsume(s: &mut Store, v1190: Term, v1168: Term, a0: Term, v2: Term, v1167: Term, v1110: Term, v1166: Term) -> CheckResult<Term> {
let v1191 = match s.builtin_core(EvalOp::Not, &[v1190]) { Ok(v) => v, Err(e) => return Err(e) };
let v1192 = match s.builtin_core(EvalOp::And, &[v1168, v1191]) { Ok(v) => v, Err(e) => return Err(e) };
let v1216 = match if_89_eo__24str_5fre_5fconsume(s, v1192, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1217 = match s.builtin_list(EvalOp::ListRev, &[v1167, v1216]) { Ok(v) => v, Err(e) => return Err(e) };
let v1218 = match eo__24str_5fre_5fconsume_5frec(s, v1110, v1166, v1217) { Ok(v) => v, Err(e) => return Err(e) };
let v1219 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v1220 = match s.builtin_core(EvalOp::Eq, &[v1218, v1219]) { Ok(v) => v, Err(e) => return Err(e) };
let v1552 = match if_117_eo__24str_5fre_5fconsume(s, v1220, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1552)
}
pub(super) fn more_123_eo__24str_5fre_5fconsume(s: &mut Store, v1175: Term, v1178: Term, a0: Term, v1173: Term, v1168: Term, v2: Term, v1167: Term, v1110: Term, v1166: Term) -> CheckResult<Term> {
let v1179 = match eo__24re_5frev_5fmap_5frev(s, v1175, v1178) { Ok(v) => v, Err(e) => return Err(e) };
let v1180 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1181 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1182 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1181, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1183 = match eo__24str_5fflatten(s, v1182) { Ok(v) => v, Err(e) => return Err(e) };
let v1184 = match s.builtin_list(EvalOp::ListRev, &[v1180, v1183]) { Ok(v) => v, Err(e) => return Err(e) };
let v1185 = match eo__24str_5fre_5fconsume_5frec(s, v1173, v1179, v1184) { Ok(v) => v, Err(e) => return Err(e) };
let v1186 = match eo__24str_5fmembership_5fre(s, v1185) { Ok(v) => v, Err(e) => return Err(e) };
let v1187 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1188 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1189 = match s.apply(v1187, v1188) { Ok(v) => v, Err(e) => return Err(e) };
let v1190 = match s.builtin_core(EvalOp::Eq, &[v1186, v1189]) { Ok(v) => v, Err(e) => return Err(e) };
more_124_eo__24str_5fre_5fconsume(s, v1190, v1168, a0, v2, v1167, v1110, v1166)
}
pub(super) fn more_122_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v2: Term, v1110: Term, v1166: Term) -> CheckResult<Term> {
let v1167 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1168 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1169 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1170 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1171 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1170, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1172 = match eo__24str_5fflatten(s, v1171) { Ok(v) => v, Err(e) => return Err(e) };
let v1173 = match s.builtin_list(EvalOp::ListRev, &[v1169, v1172]) { Ok(v) => v, Err(e) => return Err(e) };
let v1174 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1175 = match eo__24re_5fflatten(s, v1174, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1176 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1177 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1178 = match s.apply(v1176, v1177) { Ok(v) => v, Err(e) => return Err(e) };
more_123_eo__24str_5fre_5fconsume(s, v1175, v1178, a0, v1173, v1168, v2, v1167, v1110, v1166)
}
pub(super) fn more_121_eo__24str_5fre_5fconsume(s: &mut Store, v1130: Term, v1112: Term, v2: Term, a0: Term, v1111: Term, v1110: Term) -> CheckResult<Term> {
let v1131 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1132 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1133 = match s.apply(v1131, v1132) { Ok(v) => v, Err(e) => return Err(e) };
let v1134 = match s.builtin_core(EvalOp::Eq, &[v1130, v1133]) { Ok(v) => v, Err(e) => return Err(e) };
let v1135 = match s.builtin_core(EvalOp::Not, &[v1134]) { Ok(v) => v, Err(e) => return Err(e) };
let v1136 = match s.builtin_core(EvalOp::And, &[v1112, v1135]) { Ok(v) => v, Err(e) => return Err(e) };
let v1161 = match if_87_eo__24str_5fre_5fconsume(s, v1136, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v1162 = match eo__24re_5fflatten(s, v1111, v1161) { Ok(v) => v, Err(e) => return Err(e) };
let v1163 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1164 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1165 = match s.apply(v1163, v1164) { Ok(v) => v, Err(e) => return Err(e) };
let v1166 = match eo__24re_5frev_5fmap_5frev(s, v1162, v1165) { Ok(v) => v, Err(e) => return Err(e) };
more_122_eo__24str_5fre_5fconsume(s, a0, v2, v1110, v1166)
}
pub(super) fn more_120_eo__24str_5fre_5fconsume(s: &mut Store, v1118: Term, v2: Term, a0: Term, v1117: Term, v1112: Term, v1111: Term, v1110: Term) -> CheckResult<Term> {
let v1119 = match eo__24re_5fflatten(s, v1118, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1120 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1121 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1122 = match s.apply(v1120, v1121) { Ok(v) => v, Err(e) => return Err(e) };
let v1123 = match eo__24re_5frev_5fmap_5frev(s, v1119, v1122) { Ok(v) => v, Err(e) => return Err(e) };
let v1124 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1125 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1126 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1125, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1127 = match eo__24str_5fflatten(s, v1126) { Ok(v) => v, Err(e) => return Err(e) };
let v1128 = match s.builtin_list(EvalOp::ListRev, &[v1124, v1127]) { Ok(v) => v, Err(e) => return Err(e) };
let v1129 = match eo__24str_5fre_5fconsume_5frec(s, v1117, v1123, v1128) { Ok(v) => v, Err(e) => return Err(e) };
let v1130 = match eo__24str_5fmembership_5fre(s, v1129) { Ok(v) => v, Err(e) => return Err(e) };
more_121_eo__24str_5fre_5fconsume(s, v1130, v1112, v2, a0, v1111, v1110)
}
pub(super) fn more_119_eo__24str_5fre_5fconsume(s: &mut Store, v1083: Term, v1061: Term, a0: Term, v2: Term, v1060: Term) -> CheckResult<Term> {
let v1084 = match s.builtin_core(EvalOp::Not, &[v1083]) { Ok(v) => v, Err(e) => return Err(e) };
let v1085 = match s.builtin_core(EvalOp::And, &[v1061, v1084]) { Ok(v) => v, Err(e) => return Err(e) };
let v1109 = match if_85_eo__24str_5fre_5fconsume(s, v1085, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1110 = match s.builtin_list(EvalOp::ListRev, &[v1060, v1109]) { Ok(v) => v, Err(e) => return Err(e) };
let v1111 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1112 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1113 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1114 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1115 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1114, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1116 = match eo__24str_5fflatten(s, v1115) { Ok(v) => v, Err(e) => return Err(e) };
let v1117 = match s.builtin_list(EvalOp::ListRev, &[v1113, v1116]) { Ok(v) => v, Err(e) => return Err(e) };
let v1118 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_120_eo__24str_5fre_5fconsume(s, v1118, v2, a0, v1117, v1112, v1111, v1110)
}
pub(super) fn more_118_eo__24str_5fre_5fconsume(s: &mut Store, v1068: Term, v1071: Term, a0: Term, v1066: Term, v1061: Term, v2: Term, v1060: Term) -> CheckResult<Term> {
let v1072 = match eo__24re_5frev_5fmap_5frev(s, v1068, v1071) { Ok(v) => v, Err(e) => return Err(e) };
let v1073 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1074 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1075 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1074, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1076 = match eo__24str_5fflatten(s, v1075) { Ok(v) => v, Err(e) => return Err(e) };
let v1077 = match s.builtin_list(EvalOp::ListRev, &[v1073, v1076]) { Ok(v) => v, Err(e) => return Err(e) };
let v1078 = match eo__24str_5fre_5fconsume_5frec(s, v1066, v1072, v1077) { Ok(v) => v, Err(e) => return Err(e) };
let v1079 = match eo__24str_5fmembership_5fre(s, v1078) { Ok(v) => v, Err(e) => return Err(e) };
let v1080 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1081 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1082 = match s.apply(v1080, v1081) { Ok(v) => v, Err(e) => return Err(e) };
let v1083 = match s.builtin_core(EvalOp::Eq, &[v1079, v1082]) { Ok(v) => v, Err(e) => return Err(e) };
more_119_eo__24str_5fre_5fconsume(s, v1083, v1061, a0, v2, v1060)
}
pub(super) fn if_125_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1059 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1059)
}
Some(false) => {
let v1060 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1061 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1062 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1063 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1064 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1063, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1065 = match eo__24str_5fflatten(s, v1064) { Ok(v) => v, Err(e) => return Err(e) };
let v1066 = match s.builtin_list(EvalOp::ListRev, &[v1062, v1065]) { Ok(v) => v, Err(e) => return Err(e) };
let v1067 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1068 = match eo__24re_5fflatten(s, v1067, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1069 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1070 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1071 = match s.apply(v1069, v1070) { Ok(v) => v, Err(e) => return Err(e) };
more_118_eo__24str_5fre_5fconsume(s, v1068, v1071, a0, v1066, v1061, v2, v1060)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_127_eo__24str_5fre_5fconsume(s: &mut Store, v1556: Term, v2: Term, v1555: Term) -> CheckResult<Term> {
let v1557 = match s.apply(v1556, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1558 = match s.apply(v1555, v1557) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1558)
}
pub(super) fn more_126_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v1044: Term, v1050: Term, v2: Term, v1039: Term) -> CheckResult<Term> {
let v1051 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1052 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1053 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1052, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1054 = match eo__24str_5fflatten(s, v1053) { Ok(v) => v, Err(e) => return Err(e) };
let v1055 = match s.builtin_list(EvalOp::ListRev, &[v1051, v1054]) { Ok(v) => v, Err(e) => return Err(e) };
let v1056 = match eo__24str_5fre_5fconsume_5frec(s, v1044, v1050, v1055) { Ok(v) => v, Err(e) => return Err(e) };
let v1057 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v1058 = match s.builtin_core(EvalOp::Eq, &[v1056, v1057]) { Ok(v) => v, Err(e) => return Err(e) };
let v1553 = match if_125_eo__24str_5fre_5fconsume(s, v1058, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1554 = match eo__24str_5fmembership_5fstr(s, v1553) { Ok(v) => v, Err(e) => return Err(e) };
let v1555 = match s.apply(v1039, v1554) { Ok(v) => v, Err(e) => return Err(e) };
let v1556 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_127_eo__24str_5fre_5fconsume(s, v1556, v2, v1555)
}
pub(super) fn requires_128_eo__24str_5fre_5fconsume(s: &mut Store, v1035: Term, v1038: Term, a0: Term, v2: Term) -> CheckResult<Term> {
if v1035 != v1038 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v1035) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v1039 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1040 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1041 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1042 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1041, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v1043 = match eo__24str_5fflatten(s, v1042) { Ok(v) => v, Err(e) => return Err(e) };
let v1044 = match s.builtin_list(EvalOp::ListRev, &[v1040, v1043]) { Ok(v) => v, Err(e) => return Err(e) };
let v1045 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v1046 = match eo__24re_5fflatten(s, v1045, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1047 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1048 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1049 = match s.apply(v1047, v1048) { Ok(v) => v, Err(e) => return Err(e) };
let v1050 = match eo__24re_5frev_5fmap_5frev(s, v1046, v1049) { Ok(v) => v, Err(e) => return Err(e) };
more_126_eo__24str_5fre_5fconsume(s, a0, v1044, v1050, v2, v1039)
}
pub(super) fn more_130_eo__24str_5fre_5fconsume(s: &mut Store, v1035: Term, v1038: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let v1559 = match requires_128_eo__24str_5fre_5fconsume(s, v1035, v1038, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1559)
}
pub(super) fn more_129_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v532: Term, v525: Term, v531: Term, v2: Term) -> CheckResult<Term> {
let v533 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v534 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v533, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v535 = match eo__24str_5fflatten(s, v534) { Ok(v) => v, Err(e) => return Err(e) };
let v536 = match s.builtin_list(EvalOp::ListRev, &[v532, v535]) { Ok(v) => v, Err(e) => return Err(e) };
let v537 = match eo__24str_5fre_5fconsume_5frec(s, v525, v531, v536) { Ok(v) => v, Err(e) => return Err(e) };
let v538 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v539 = match s.builtin_core(EvalOp::Eq, &[v537, v538]) { Ok(v) => v, Err(e) => return Err(e) };
let v1034 = match if_83_eo__24str_5fre_5fconsume(s, v539, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v1035 = match eo__24str_5fmembership_5fre(s, v1034) { Ok(v) => v, Err(e) => return Err(e) };
let v1036 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1037 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v1038 = match s.apply(v1036, v1037) { Ok(v) => v, Err(e) => return Err(e) };
more_130_eo__24str_5fre_5fconsume(s, v1035, v1038, a0, v2)
}
pub(super) fn if_131_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v520 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v520)
}
Some(false) => {
let v521 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v522 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v523 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v522, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v524 = match eo__24str_5fflatten(s, v523) { Ok(v) => v, Err(e) => return Err(e) };
let v525 = match s.builtin_list(EvalOp::ListRev, &[v521, v524]) { Ok(v) => v, Err(e) => return Err(e) };
let v526 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v527 = match eo__24re_5fflatten(s, v526, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v528 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v529 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v530 = match s.apply(v528, v529) { Ok(v) => v, Err(e) => return Err(e) };
let v531 = match eo__24re_5frev_5fmap_5frev(s, v527, v530) { Ok(v) => v, Err(e) => return Err(e) };
let v532 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_129_eo__24str_5fre_5fconsume(s, a0, v532, v525, v531, v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_133_eo__24str_5fre_5fconsume(s: &mut Store, v517: Term, v518: Term, a0: Term, v2: Term) -> CheckResult<Option<Term>> {
let v519 = match s.builtin_core(EvalOp::Eq, &[v517, v518]) { Ok(v) => v, Err(e) => return Err(e) };
let v1560 = match if_131_eo__24str_5fre_5fconsume(s, v519, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1560))
}
pub(super) fn more_132_eo__24str_5fre_5fconsume(s: &mut Store, v11: Term, v12: Term, v10: Term, a0: Term, v8: Term, v2: Term) -> CheckResult<Option<Term>> {
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24re_5frev_5fmap_5frev(s, v10, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v16, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match eo__24str_5fflatten(s, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.builtin_list(EvalOp::ListRev, &[v15, v18]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match eo__24str_5fre_5fconsume_5frec(s, v8, v14, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Eq, &[v20, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v517 = match if_41_eo__24str_5fre_5fconsume(s, v22, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v518 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
more_133_eo__24str_5fre_5fconsume(s, v517, v518, a0, v2)
}
pub(super) fn case_0_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v5, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match eo__24str_5fflatten(s, v6) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.builtin_list(EvalOp::ListRev, &[v4, v7]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5fflatten(s, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_132_eo__24str_5fre_5fconsume(s, v11, v12, v10, a0, v8, v2)
}
pub(super) fn more_134_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v62: Term, v55: Term, v61: Term) -> CheckResult<Term> {
let v63 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v63, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v65 = match eo__24str_5fflatten(s, v64) { Ok(v) => v, Err(e) => return Err(e) };
let v66 = match s.builtin_list(EvalOp::ListRev, &[v62, v65]) { Ok(v) => v, Err(e) => return Err(e) };
let v67 = match eo__24str_5fre_5fconsume_5frec(s, v55, v61, v66) { Ok(v) => v, Err(e) => return Err(e) };
let v68 = match eo__24str_5fmembership_5fstr(s, v67) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v68)
}
pub(super) fn if_135_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v46 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v47, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match eo__24str_5fflatten(s, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.builtin_list(EvalOp::ListRev, &[v46, v49]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v50)
}
Some(false) => {
let v51 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v52, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match eo__24str_5fflatten(s, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.builtin_list(EvalOp::ListRev, &[v51, v54]) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match eo__24re_5fflatten(s, v56, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.apply(v58, v59) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match eo__24re_5frev_5fmap_5frev(s, v57, v60) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_134_eo__24str_5fre_5fconsume(s, a0, v62, v55, v61)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_136_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v114: Term, v107: Term, v113: Term) -> CheckResult<Term> {
let v115 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v116 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v115, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v117 = match eo__24str_5fflatten(s, v116) { Ok(v) => v, Err(e) => return Err(e) };
let v118 = match s.builtin_list(EvalOp::ListRev, &[v114, v117]) { Ok(v) => v, Err(e) => return Err(e) };
let v119 = match eo__24str_5fre_5fconsume_5frec(s, v107, v113, v118) { Ok(v) => v, Err(e) => return Err(e) };
let v120 = match eo__24str_5fmembership_5fre(s, v119) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v120)
}
pub(super) fn if_137_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a1: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v97 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v98 = match eo__24re_5fflatten(s, v97, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v99 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v100 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v101 = match s.apply(v99, v100) { Ok(v) => v, Err(e) => return Err(e) };
let v102 = match eo__24re_5frev_5fmap_5frev(s, v98, v101) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v102)
}
Some(false) => {
let v103 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v104 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v105 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v104, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v106 = match eo__24str_5fflatten(s, v105) { Ok(v) => v, Err(e) => return Err(e) };
let v107 = match s.builtin_list(EvalOp::ListRev, &[v103, v106]) { Ok(v) => v, Err(e) => return Err(e) };
let v108 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v109 = match eo__24re_5fflatten(s, v108, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v110 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v111 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v112 = match s.apply(v110, v111) { Ok(v) => v, Err(e) => return Err(e) };
let v113 = match eo__24re_5frev_5fmap_5frev(s, v109, v112) { Ok(v) => v, Err(e) => return Err(e) };
let v114 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_136_eo__24str_5fre_5fconsume(s, a0, v114, v107, v113)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_138_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v169: Term, v162: Term, v168: Term) -> CheckResult<Term> {
let v170 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v171 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v170, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v172 = match eo__24str_5fflatten(s, v171) { Ok(v) => v, Err(e) => return Err(e) };
let v173 = match s.builtin_list(EvalOp::ListRev, &[v169, v172]) { Ok(v) => v, Err(e) => return Err(e) };
let v174 = match eo__24str_5fre_5fconsume_5frec(s, v162, v168, v173) { Ok(v) => v, Err(e) => return Err(e) };
let v175 = match eo__24str_5fmembership_5fstr(s, v174) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v175)
}
pub(super) fn if_139_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v153 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v154 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v155 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v154, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v156 = match eo__24str_5fflatten(s, v155) { Ok(v) => v, Err(e) => return Err(e) };
let v157 = match s.builtin_list(EvalOp::ListRev, &[v153, v156]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v157)
}
Some(false) => {
let v158 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v159 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v160 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v159, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v161 = match eo__24str_5fflatten(s, v160) { Ok(v) => v, Err(e) => return Err(e) };
let v162 = match s.builtin_list(EvalOp::ListRev, &[v158, v161]) { Ok(v) => v, Err(e) => return Err(e) };
let v163 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v164 = match eo__24re_5fflatten(s, v163, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v165 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v166 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v167 = match s.apply(v165, v166) { Ok(v) => v, Err(e) => return Err(e) };
let v168 = match eo__24re_5frev_5fmap_5frev(s, v164, v167) { Ok(v) => v, Err(e) => return Err(e) };
let v169 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_138_eo__24str_5fre_5fconsume(s, a0, v169, v162, v168)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_140_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v226: Term, v219: Term, v225: Term) -> CheckResult<Term> {
let v227 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v228 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v227, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v229 = match eo__24str_5fflatten(s, v228) { Ok(v) => v, Err(e) => return Err(e) };
let v230 = match s.builtin_list(EvalOp::ListRev, &[v226, v229]) { Ok(v) => v, Err(e) => return Err(e) };
let v231 = match eo__24str_5fre_5fconsume_5frec(s, v219, v225, v230) { Ok(v) => v, Err(e) => return Err(e) };
let v232 = match eo__24str_5fmembership_5fstr(s, v231) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v232)
}
pub(super) fn if_141_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v210 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v211 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v212 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v211, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v213 = match eo__24str_5fflatten(s, v212) { Ok(v) => v, Err(e) => return Err(e) };
let v214 = match s.builtin_list(EvalOp::ListRev, &[v210, v213]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v214)
}
Some(false) => {
let v215 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v216 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v217 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v216, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v218 = match eo__24str_5fflatten(s, v217) { Ok(v) => v, Err(e) => return Err(e) };
let v219 = match s.builtin_list(EvalOp::ListRev, &[v215, v218]) { Ok(v) => v, Err(e) => return Err(e) };
let v220 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v221 = match eo__24re_5fflatten(s, v220, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v222 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v223 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v224 = match s.apply(v222, v223) { Ok(v) => v, Err(e) => return Err(e) };
let v225 = match eo__24re_5frev_5fmap_5frev(s, v221, v224) { Ok(v) => v, Err(e) => return Err(e) };
let v226 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_140_eo__24str_5fre_5fconsume(s, a0, v226, v219, v225)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_142_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v278: Term, v271: Term, v277: Term) -> CheckResult<Term> {
let v279 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v280 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v279, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v281 = match eo__24str_5fflatten(s, v280) { Ok(v) => v, Err(e) => return Err(e) };
let v282 = match s.builtin_list(EvalOp::ListRev, &[v278, v281]) { Ok(v) => v, Err(e) => return Err(e) };
let v283 = match eo__24str_5fre_5fconsume_5frec(s, v271, v277, v282) { Ok(v) => v, Err(e) => return Err(e) };
let v284 = match eo__24str_5fmembership_5fre(s, v283) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v284)
}
pub(super) fn if_143_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a1: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v261 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v262 = match eo__24re_5fflatten(s, v261, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v263 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v264 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v265 = match s.apply(v263, v264) { Ok(v) => v, Err(e) => return Err(e) };
let v266 = match eo__24re_5frev_5fmap_5frev(s, v262, v265) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v266)
}
Some(false) => {
let v267 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v268 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v269 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v268, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v270 = match eo__24str_5fflatten(s, v269) { Ok(v) => v, Err(e) => return Err(e) };
let v271 = match s.builtin_list(EvalOp::ListRev, &[v267, v270]) { Ok(v) => v, Err(e) => return Err(e) };
let v272 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v273 = match eo__24re_5fflatten(s, v272, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v274 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v275 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v276 = match s.apply(v274, v275) { Ok(v) => v, Err(e) => return Err(e) };
let v277 = match eo__24re_5frev_5fmap_5frev(s, v273, v276) { Ok(v) => v, Err(e) => return Err(e) };
let v278 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_142_eo__24str_5fre_5fconsume(s, a0, v278, v271, v277)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_144_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v333: Term, v326: Term, v332: Term) -> CheckResult<Term> {
let v334 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v335 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v334, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v336 = match eo__24str_5fflatten(s, v335) { Ok(v) => v, Err(e) => return Err(e) };
let v337 = match s.builtin_list(EvalOp::ListRev, &[v333, v336]) { Ok(v) => v, Err(e) => return Err(e) };
let v338 = match eo__24str_5fre_5fconsume_5frec(s, v326, v332, v337) { Ok(v) => v, Err(e) => return Err(e) };
let v339 = match eo__24str_5fmembership_5fstr(s, v338) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v339)
}
pub(super) fn if_145_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v317 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v318 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v319 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v318, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v320 = match eo__24str_5fflatten(s, v319) { Ok(v) => v, Err(e) => return Err(e) };
let v321 = match s.builtin_list(EvalOp::ListRev, &[v317, v320]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v321)
}
Some(false) => {
let v322 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v323 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v324 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v323, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v325 = match eo__24str_5fflatten(s, v324) { Ok(v) => v, Err(e) => return Err(e) };
let v326 = match s.builtin_list(EvalOp::ListRev, &[v322, v325]) { Ok(v) => v, Err(e) => return Err(e) };
let v327 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v328 = match eo__24re_5fflatten(s, v327, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v329 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v330 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v331 = match s.apply(v329, v330) { Ok(v) => v, Err(e) => return Err(e) };
let v332 = match eo__24re_5frev_5fmap_5frev(s, v328, v331) { Ok(v) => v, Err(e) => return Err(e) };
let v333 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_144_eo__24str_5fre_5fconsume(s, a0, v333, v326, v332)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_146_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v391: Term, v384: Term, v390: Term) -> CheckResult<Term> {
let v392 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v393 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v392, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v394 = match eo__24str_5fflatten(s, v393) { Ok(v) => v, Err(e) => return Err(e) };
let v395 = match s.builtin_list(EvalOp::ListRev, &[v391, v394]) { Ok(v) => v, Err(e) => return Err(e) };
let v396 = match eo__24str_5fre_5fconsume_5frec(s, v384, v390, v395) { Ok(v) => v, Err(e) => return Err(e) };
let v397 = match eo__24str_5fmembership_5fstr(s, v396) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v397)
}
pub(super) fn if_147_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v375 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v376 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v377 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v376, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v378 = match eo__24str_5fflatten(s, v377) { Ok(v) => v, Err(e) => return Err(e) };
let v379 = match s.builtin_list(EvalOp::ListRev, &[v375, v378]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v379)
}
Some(false) => {
let v380 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v381 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v382 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v381, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v383 = match eo__24str_5fflatten(s, v382) { Ok(v) => v, Err(e) => return Err(e) };
let v384 = match s.builtin_list(EvalOp::ListRev, &[v380, v383]) { Ok(v) => v, Err(e) => return Err(e) };
let v385 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v386 = match eo__24re_5fflatten(s, v385, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v387 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v388 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v389 = match s.apply(v387, v388) { Ok(v) => v, Err(e) => return Err(e) };
let v390 = match eo__24re_5frev_5fmap_5frev(s, v386, v389) { Ok(v) => v, Err(e) => return Err(e) };
let v391 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_146_eo__24str_5fre_5fconsume(s, a0, v391, v384, v390)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_148_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v443: Term, v436: Term, v442: Term) -> CheckResult<Term> {
let v444 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v445 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v444, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v446 = match eo__24str_5fflatten(s, v445) { Ok(v) => v, Err(e) => return Err(e) };
let v447 = match s.builtin_list(EvalOp::ListRev, &[v443, v446]) { Ok(v) => v, Err(e) => return Err(e) };
let v448 = match eo__24str_5fre_5fconsume_5frec(s, v436, v442, v447) { Ok(v) => v, Err(e) => return Err(e) };
let v449 = match eo__24str_5fmembership_5fre(s, v448) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v449)
}
pub(super) fn if_149_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a1: Term, a0: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v426 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v427 = match eo__24re_5fflatten(s, v426, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v428 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v429 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v430 = match s.apply(v428, v429) { Ok(v) => v, Err(e) => return Err(e) };
let v431 = match eo__24re_5frev_5fmap_5frev(s, v427, v430) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v431)
}
Some(false) => {
let v432 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v433 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v434 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v433, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v435 = match eo__24str_5fflatten(s, v434) { Ok(v) => v, Err(e) => return Err(e) };
let v436 = match s.builtin_list(EvalOp::ListRev, &[v432, v435]) { Ok(v) => v, Err(e) => return Err(e) };
let v437 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v438 = match eo__24re_5fflatten(s, v437, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v439 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v440 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v441 = match s.apply(v439, v440) { Ok(v) => v, Err(e) => return Err(e) };
let v442 = match eo__24re_5frev_5fmap_5frev(s, v438, v441) { Ok(v) => v, Err(e) => return Err(e) };
let v443 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_148_eo__24str_5fre_5fconsume(s, a0, v443, v436, v442)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_150_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v498: Term, v491: Term, v497: Term) -> CheckResult<Term> {
let v499 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v500 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v499, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v501 = match eo__24str_5fflatten(s, v500) { Ok(v) => v, Err(e) => return Err(e) };
let v502 = match s.builtin_list(EvalOp::ListRev, &[v498, v501]) { Ok(v) => v, Err(e) => return Err(e) };
let v503 = match eo__24str_5fre_5fconsume_5frec(s, v491, v497, v502) { Ok(v) => v, Err(e) => return Err(e) };
let v504 = match eo__24str_5fmembership_5fstr(s, v503) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v504)
}
pub(super) fn if_151_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v482 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v483 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v484 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v483, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v485 = match eo__24str_5fflatten(s, v484) { Ok(v) => v, Err(e) => return Err(e) };
let v486 = match s.builtin_list(EvalOp::ListRev, &[v482, v485]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v486)
}
Some(false) => {
let v487 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v488 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v489 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v488, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v490 = match eo__24str_5fflatten(s, v489) { Ok(v) => v, Err(e) => return Err(e) };
let v491 = match s.builtin_list(EvalOp::ListRev, &[v487, v490]) { Ok(v) => v, Err(e) => return Err(e) };
let v492 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v493 = match eo__24re_5fflatten(s, v492, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v494 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v495 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v496 = match s.apply(v494, v495) { Ok(v) => v, Err(e) => return Err(e) };
let v497 = match eo__24re_5frev_5fmap_5frev(s, v493, v496) { Ok(v) => v, Err(e) => return Err(e) };
let v498 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_150_eo__24str_5fre_5fconsume(s, a0, v498, v491, v497)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_166_eo__24str_5fre_5fconsume(s: &mut Store, v475: Term, v478: Term, v457: Term, a0: Term, a1: Term, v456: Term, v399: Term, v455: Term, v348: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v479 = match s.builtin_core(EvalOp::Eq, &[v475, v478]) { Ok(v) => v, Err(e) => return Err(e) };
let v480 = match s.builtin_core(EvalOp::Not, &[v479]) { Ok(v) => v, Err(e) => return Err(e) };
let v481 = match s.builtin_core(EvalOp::And, &[v457, v480]) { Ok(v) => v, Err(e) => return Err(e) };
let v505 = match if_151_eo__24str_5fre_5fconsume(s, v481, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v506 = match s.builtin_list(EvalOp::ListRev, &[v456, v505]) { Ok(v) => v, Err(e) => return Err(e) };
let v507 = match eo__24str_5fre_5fconsume_5frec(s, v399, v455, v506) { Ok(v) => v, Err(e) => return Err(e) };
let v508 = match eo__24str_5fmembership_5fre(s, v507) { Ok(v) => v, Err(e) => return Err(e) };
let v509 = match eo__24re_5funflatten(s, v348, v508) { Ok(v) => v, Err(e) => return Err(e) };
let v510 = match s.builtin_list(EvalOp::ListSingletonElim, &[v347, v509]) { Ok(v) => v, Err(e) => return Err(e) };
let v511 = match s.apply(v346, v510) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v511)
}
pub(super) fn more_165_eo__24str_5fre_5fconsume(s: &mut Store, v465: Term, v466: Term, v464: Term, a0: Term, v462: Term, v457: Term, a1: Term, v456: Term, v399: Term, v455: Term, v348: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v467 = match s.apply(v465, v466) { Ok(v) => v, Err(e) => return Err(e) };
let v468 = match eo__24re_5frev_5fmap_5frev(s, v464, v467) { Ok(v) => v, Err(e) => return Err(e) };
let v469 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v470 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v471 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v470, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v472 = match eo__24str_5fflatten(s, v471) { Ok(v) => v, Err(e) => return Err(e) };
let v473 = match s.builtin_list(EvalOp::ListRev, &[v469, v472]) { Ok(v) => v, Err(e) => return Err(e) };
let v474 = match eo__24str_5fre_5fconsume_5frec(s, v462, v468, v473) { Ok(v) => v, Err(e) => return Err(e) };
let v475 = match eo__24str_5fmembership_5fre(s, v474) { Ok(v) => v, Err(e) => return Err(e) };
let v476 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v477 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v478 = match s.apply(v476, v477) { Ok(v) => v, Err(e) => return Err(e) };
more_166_eo__24str_5fre_5fconsume(s, v475, v478, v457, a0, a1, v456, v399, v455, v348, v347, v346)
}
pub(super) fn more_164_eo__24str_5fre_5fconsume(s: &mut Store, v451: Term, v454: Term, a0: Term, a1: Term, v399: Term, v348: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v455 = match eo__24re_5frev_5fmap_5frev(s, v451, v454) { Ok(v) => v, Err(e) => return Err(e) };
let v456 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v457 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v458 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v459 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v460 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v459, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v461 = match eo__24str_5fflatten(s, v460) { Ok(v) => v, Err(e) => return Err(e) };
let v462 = match s.builtin_list(EvalOp::ListRev, &[v458, v461]) { Ok(v) => v, Err(e) => return Err(e) };
let v463 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v464 = match eo__24re_5fflatten(s, v463, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v465 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v466 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_165_eo__24str_5fre_5fconsume(s, v465, v466, v464, a0, v462, v457, a1, v456, v399, v455, v348, v347, v346)
}
pub(super) fn more_163_eo__24str_5fre_5fconsume(s: &mut Store, v418: Term, v401: Term, a1: Term, a0: Term, v400: Term, v399: Term, v348: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v419 = match eo__24str_5fmembership_5fre(s, v418) { Ok(v) => v, Err(e) => return Err(e) };
let v420 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v421 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v422 = match s.apply(v420, v421) { Ok(v) => v, Err(e) => return Err(e) };
let v423 = match s.builtin_core(EvalOp::Eq, &[v419, v422]) { Ok(v) => v, Err(e) => return Err(e) };
let v424 = match s.builtin_core(EvalOp::Not, &[v423]) { Ok(v) => v, Err(e) => return Err(e) };
let v425 = match s.builtin_core(EvalOp::And, &[v401, v424]) { Ok(v) => v, Err(e) => return Err(e) };
let v450 = match if_149_eo__24str_5fre_5fconsume(s, v425, a1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v451 = match eo__24re_5fflatten(s, v400, v450) { Ok(v) => v, Err(e) => return Err(e) };
let v452 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v453 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v454 = match s.apply(v452, v453) { Ok(v) => v, Err(e) => return Err(e) };
more_164_eo__24str_5fre_5fconsume(s, v451, v454, a0, a1, v399, v348, v347, v346)
}
pub(super) fn more_162_eo__24str_5fre_5fconsume(s: &mut Store, a1: Term, a0: Term, v406: Term, v401: Term, v400: Term, v399: Term, v348: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v407 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v408 = match eo__24re_5fflatten(s, v407, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v409 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v410 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v411 = match s.apply(v409, v410) { Ok(v) => v, Err(e) => return Err(e) };
let v412 = match eo__24re_5frev_5fmap_5frev(s, v408, v411) { Ok(v) => v, Err(e) => return Err(e) };
let v413 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v414 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v415 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v414, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v416 = match eo__24str_5fflatten(s, v415) { Ok(v) => v, Err(e) => return Err(e) };
let v417 = match s.builtin_list(EvalOp::ListRev, &[v413, v416]) { Ok(v) => v, Err(e) => return Err(e) };
let v418 = match eo__24str_5fre_5fconsume_5frec(s, v406, v412, v417) { Ok(v) => v, Err(e) => return Err(e) };
more_163_eo__24str_5fre_5fconsume(s, v418, v401, a1, a0, v400, v399, v348, v347, v346)
}
pub(super) fn more_161_eo__24str_5fre_5fconsume(s: &mut Store, v368: Term, v371: Term, v350: Term, a0: Term, a1: Term, v349: Term, v348: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v372 = match s.builtin_core(EvalOp::Eq, &[v368, v371]) { Ok(v) => v, Err(e) => return Err(e) };
let v373 = match s.builtin_core(EvalOp::Not, &[v372]) { Ok(v) => v, Err(e) => return Err(e) };
let v374 = match s.builtin_core(EvalOp::And, &[v350, v373]) { Ok(v) => v, Err(e) => return Err(e) };
let v398 = match if_147_eo__24str_5fre_5fconsume(s, v374, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v399 = match s.builtin_list(EvalOp::ListRev, &[v349, v398]) { Ok(v) => v, Err(e) => return Err(e) };
let v400 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v401 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v402 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v403 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v404 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v403, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v405 = match eo__24str_5fflatten(s, v404) { Ok(v) => v, Err(e) => return Err(e) };
let v406 = match s.builtin_list(EvalOp::ListRev, &[v402, v405]) { Ok(v) => v, Err(e) => return Err(e) };
more_162_eo__24str_5fre_5fconsume(s, a1, a0, v406, v401, v400, v399, v348, v347, v346)
}
pub(super) fn more_160_eo__24str_5fre_5fconsume(s: &mut Store, v358: Term, v359: Term, v357: Term, a0: Term, v355: Term, v350: Term, a1: Term, v349: Term, v348: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v360 = match s.apply(v358, v359) { Ok(v) => v, Err(e) => return Err(e) };
let v361 = match eo__24re_5frev_5fmap_5frev(s, v357, v360) { Ok(v) => v, Err(e) => return Err(e) };
let v362 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v363 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v364 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v363, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v365 = match eo__24str_5fflatten(s, v364) { Ok(v) => v, Err(e) => return Err(e) };
let v366 = match s.builtin_list(EvalOp::ListRev, &[v362, v365]) { Ok(v) => v, Err(e) => return Err(e) };
let v367 = match eo__24str_5fre_5fconsume_5frec(s, v355, v361, v366) { Ok(v) => v, Err(e) => return Err(e) };
let v368 = match eo__24str_5fmembership_5fre(s, v367) { Ok(v) => v, Err(e) => return Err(e) };
let v369 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v370 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v371 = match s.apply(v369, v370) { Ok(v) => v, Err(e) => return Err(e) };
more_161_eo__24str_5fre_5fconsume(s, v368, v371, v350, a0, a1, v349, v348, v347, v346)
}
pub(super) fn more_159_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, a1: Term, v347: Term, v346: Term) -> CheckResult<Term> {
let v348 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v349 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v350 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v351 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v352 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v353 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v352, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v354 = match eo__24str_5fflatten(s, v353) { Ok(v) => v, Err(e) => return Err(e) };
let v355 = match s.builtin_list(EvalOp::ListRev, &[v351, v354]) { Ok(v) => v, Err(e) => return Err(e) };
let v356 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v357 = match eo__24re_5fflatten(s, v356, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v358 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v359 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_160_eo__24str_5fre_5fconsume(s, v358, v359, v357, a0, v355, v350, a1, v349, v348, v347, v346)
}
pub(super) fn more_158_eo__24str_5fre_5fconsume(s: &mut Store, v311: Term, v312: Term, v310: Term, v292: Term, a0: Term, a1: Term, v291: Term, v234: Term, v290: Term, v183: Term, v182: Term) -> CheckResult<Term> {
let v313 = match s.apply(v311, v312) { Ok(v) => v, Err(e) => return Err(e) };
let v314 = match s.builtin_core(EvalOp::Eq, &[v310, v313]) { Ok(v) => v, Err(e) => return Err(e) };
let v315 = match s.builtin_core(EvalOp::Not, &[v314]) { Ok(v) => v, Err(e) => return Err(e) };
let v316 = match s.builtin_core(EvalOp::And, &[v292, v315]) { Ok(v) => v, Err(e) => return Err(e) };
let v340 = match if_145_eo__24str_5fre_5fconsume(s, v316, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v341 = match s.builtin_list(EvalOp::ListRev, &[v291, v340]) { Ok(v) => v, Err(e) => return Err(e) };
let v342 = match eo__24str_5fre_5fconsume_5frec(s, v234, v290, v341) { Ok(v) => v, Err(e) => return Err(e) };
let v343 = match eo__24str_5fmembership_5fstr(s, v342) { Ok(v) => v, Err(e) => return Err(e) };
let v344 = match eo__24str_5fcollect(s, v343) { Ok(v) => v, Err(e) => return Err(e) };
let v345 = match s.builtin_list(EvalOp::ListSingletonElim, &[v183, v344]) { Ok(v) => v, Err(e) => return Err(e) };
let v346 = match s.apply(v182, v345) { Ok(v) => v, Err(e) => return Err(e) };
let v347 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_159_eo__24str_5fre_5fconsume(s, a0, a1, v347, v346)
}
pub(super) fn more_157_eo__24str_5fre_5fconsume(s: &mut Store, v300: Term, v299: Term, a0: Term, v297: Term, v292: Term, a1: Term, v291: Term, v234: Term, v290: Term, v183: Term, v182: Term) -> CheckResult<Term> {
let v301 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v302 = match s.apply(v300, v301) { Ok(v) => v, Err(e) => return Err(e) };
let v303 = match eo__24re_5frev_5fmap_5frev(s, v299, v302) { Ok(v) => v, Err(e) => return Err(e) };
let v304 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v305 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v306 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v305, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v307 = match eo__24str_5fflatten(s, v306) { Ok(v) => v, Err(e) => return Err(e) };
let v308 = match s.builtin_list(EvalOp::ListRev, &[v304, v307]) { Ok(v) => v, Err(e) => return Err(e) };
let v309 = match eo__24str_5fre_5fconsume_5frec(s, v297, v303, v308) { Ok(v) => v, Err(e) => return Err(e) };
let v310 = match eo__24str_5fmembership_5fre(s, v309) { Ok(v) => v, Err(e) => return Err(e) };
let v311 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v312 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_158_eo__24str_5fre_5fconsume(s, v311, v312, v310, v292, a0, a1, v291, v234, v290, v183, v182)
}
pub(super) fn more_156_eo__24str_5fre_5fconsume(s: &mut Store, v287: Term, v288: Term, v286: Term, a0: Term, a1: Term, v234: Term, v183: Term, v182: Term) -> CheckResult<Term> {
let v289 = match s.apply(v287, v288) { Ok(v) => v, Err(e) => return Err(e) };
let v290 = match eo__24re_5frev_5fmap_5frev(s, v286, v289) { Ok(v) => v, Err(e) => return Err(e) };
let v291 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v292 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v293 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v294 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v295 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v294, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v296 = match eo__24str_5fflatten(s, v295) { Ok(v) => v, Err(e) => return Err(e) };
let v297 = match s.builtin_list(EvalOp::ListRev, &[v293, v296]) { Ok(v) => v, Err(e) => return Err(e) };
let v298 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v299 = match eo__24re_5fflatten(s, v298, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v300 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_157_eo__24str_5fre_5fconsume(s, v300, v299, a0, v297, v292, a1, v291, v234, v290, v183, v182)
}
pub(super) fn more_155_eo__24str_5fre_5fconsume(s: &mut Store, v241: Term, v247: Term, v252: Term, v236: Term, a1: Term, a0: Term, v235: Term, v234: Term, v183: Term, v182: Term) -> CheckResult<Term> {
let v253 = match eo__24str_5fre_5fconsume_5frec(s, v241, v247, v252) { Ok(v) => v, Err(e) => return Err(e) };
let v254 = match eo__24str_5fmembership_5fre(s, v253) { Ok(v) => v, Err(e) => return Err(e) };
let v255 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v256 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v257 = match s.apply(v255, v256) { Ok(v) => v, Err(e) => return Err(e) };
let v258 = match s.builtin_core(EvalOp::Eq, &[v254, v257]) { Ok(v) => v, Err(e) => return Err(e) };
let v259 = match s.builtin_core(EvalOp::Not, &[v258]) { Ok(v) => v, Err(e) => return Err(e) };
let v260 = match s.builtin_core(EvalOp::And, &[v236, v259]) { Ok(v) => v, Err(e) => return Err(e) };
let v285 = match if_143_eo__24str_5fre_5fconsume(s, v260, a1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v286 = match eo__24re_5fflatten(s, v235, v285) { Ok(v) => v, Err(e) => return Err(e) };
let v287 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v288 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_156_eo__24str_5fre_5fconsume(s, v287, v288, v286, a0, a1, v234, v183, v182)
}
pub(super) fn more_154_eo__24str_5fre_5fconsume(s: &mut Store, v237: Term, v240: Term, a1: Term, a0: Term, v236: Term, v235: Term, v234: Term, v183: Term, v182: Term) -> CheckResult<Term> {
let v241 = match s.builtin_list(EvalOp::ListRev, &[v237, v240]) { Ok(v) => v, Err(e) => return Err(e) };
let v242 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v243 = match eo__24re_5fflatten(s, v242, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v244 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v245 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v246 = match s.apply(v244, v245) { Ok(v) => v, Err(e) => return Err(e) };
let v247 = match eo__24re_5frev_5fmap_5frev(s, v243, v246) { Ok(v) => v, Err(e) => return Err(e) };
let v248 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v249 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v250 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v249, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v251 = match eo__24str_5fflatten(s, v250) { Ok(v) => v, Err(e) => return Err(e) };
let v252 = match s.builtin_list(EvalOp::ListRev, &[v248, v251]) { Ok(v) => v, Err(e) => return Err(e) };
more_155_eo__24str_5fre_5fconsume(s, v241, v247, v252, v236, a1, a0, v235, v234, v183, v182)
}
pub(super) fn more_153_eo__24str_5fre_5fconsume(s: &mut Store, v204: Term, v205: Term, v203: Term, v185: Term, a0: Term, a1: Term, v184: Term, v183: Term, v182: Term) -> CheckResult<Term> {
let v206 = match s.apply(v204, v205) { Ok(v) => v, Err(e) => return Err(e) };
let v207 = match s.builtin_core(EvalOp::Eq, &[v203, v206]) { Ok(v) => v, Err(e) => return Err(e) };
let v208 = match s.builtin_core(EvalOp::Not, &[v207]) { Ok(v) => v, Err(e) => return Err(e) };
let v209 = match s.builtin_core(EvalOp::And, &[v185, v208]) { Ok(v) => v, Err(e) => return Err(e) };
let v233 = match if_141_eo__24str_5fre_5fconsume(s, v209, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v234 = match s.builtin_list(EvalOp::ListRev, &[v184, v233]) { Ok(v) => v, Err(e) => return Err(e) };
let v235 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v236 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v237 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v238 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v239 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v238, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v240 = match eo__24str_5fflatten(s, v239) { Ok(v) => v, Err(e) => return Err(e) };
more_154_eo__24str_5fre_5fconsume(s, v237, v240, a1, a0, v236, v235, v234, v183, v182)
}
pub(super) fn more_152_eo__24str_5fre_5fconsume(s: &mut Store, v193: Term, v192: Term, a0: Term, v190: Term, v185: Term, a1: Term, v184: Term, v183: Term, v182: Term) -> CheckResult<Term> {
let v194 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v195 = match s.apply(v193, v194) { Ok(v) => v, Err(e) => return Err(e) };
let v196 = match eo__24re_5frev_5fmap_5frev(s, v192, v195) { Ok(v) => v, Err(e) => return Err(e) };
let v197 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v198 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v199 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v198, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v200 = match eo__24str_5fflatten(s, v199) { Ok(v) => v, Err(e) => return Err(e) };
let v201 = match s.builtin_list(EvalOp::ListRev, &[v197, v200]) { Ok(v) => v, Err(e) => return Err(e) };
let v202 = match eo__24str_5fre_5fconsume_5frec(s, v190, v196, v201) { Ok(v) => v, Err(e) => return Err(e) };
let v203 = match eo__24str_5fmembership_5fre(s, v202) { Ok(v) => v, Err(e) => return Err(e) };
let v204 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v205 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_153_eo__24str_5fre_5fconsume(s, v204, v205, v203, v185, a0, a1, v184, v183, v182)
}
pub(super) fn if_167_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v181 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v181)
}
Some(false) => {
let v182 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v183 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v184 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v185 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v186 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v187 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v188 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v187, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v189 = match eo__24str_5fflatten(s, v188) { Ok(v) => v, Err(e) => return Err(e) };
let v190 = match s.builtin_list(EvalOp::ListRev, &[v186, v189]) { Ok(v) => v, Err(e) => return Err(e) };
let v191 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v192 = match eo__24re_5fflatten(s, v191, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v193 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_152_eo__24str_5fre_5fconsume(s, v193, v192, a0, v190, v185, a1, v184, v183, v182)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_174_eo__24str_5fre_5fconsume(s: &mut Store, v150: Term, v128: Term, a0: Term, a1: Term, v127: Term, v70: Term, v126: Term) -> CheckResult<Term> {
let v151 = match s.builtin_core(EvalOp::Not, &[v150]) { Ok(v) => v, Err(e) => return Err(e) };
let v152 = match s.builtin_core(EvalOp::And, &[v128, v151]) { Ok(v) => v, Err(e) => return Err(e) };
let v176 = match if_139_eo__24str_5fre_5fconsume(s, v152, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v177 = match s.builtin_list(EvalOp::ListRev, &[v127, v176]) { Ok(v) => v, Err(e) => return Err(e) };
let v178 = match eo__24str_5fre_5fconsume_5frec(s, v70, v126, v177) { Ok(v) => v, Err(e) => return Err(e) };
let v179 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v180 = match s.builtin_core(EvalOp::Eq, &[v178, v179]) { Ok(v) => v, Err(e) => return Err(e) };
let v512 = match if_167_eo__24str_5fre_5fconsume(s, v180, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v512)
}
pub(super) fn more_173_eo__24str_5fre_5fconsume(s: &mut Store, v135: Term, v138: Term, a0: Term, v133: Term, v128: Term, a1: Term, v127: Term, v70: Term, v126: Term) -> CheckResult<Term> {
let v139 = match eo__24re_5frev_5fmap_5frev(s, v135, v138) { Ok(v) => v, Err(e) => return Err(e) };
let v140 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v141 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v142 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v141, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v143 = match eo__24str_5fflatten(s, v142) { Ok(v) => v, Err(e) => return Err(e) };
let v144 = match s.builtin_list(EvalOp::ListRev, &[v140, v143]) { Ok(v) => v, Err(e) => return Err(e) };
let v145 = match eo__24str_5fre_5fconsume_5frec(s, v133, v139, v144) { Ok(v) => v, Err(e) => return Err(e) };
let v146 = match eo__24str_5fmembership_5fre(s, v145) { Ok(v) => v, Err(e) => return Err(e) };
let v147 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v148 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v149 = match s.apply(v147, v148) { Ok(v) => v, Err(e) => return Err(e) };
let v150 = match s.builtin_core(EvalOp::Eq, &[v146, v149]) { Ok(v) => v, Err(e) => return Err(e) };
more_174_eo__24str_5fre_5fconsume(s, v150, v128, a0, a1, v127, v70, v126)
}
pub(super) fn more_172_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, a1: Term, v70: Term, v126: Term) -> CheckResult<Term> {
let v127 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v128 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v129 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v130 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v131 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v130, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v132 = match eo__24str_5fflatten(s, v131) { Ok(v) => v, Err(e) => return Err(e) };
let v133 = match s.builtin_list(EvalOp::ListRev, &[v129, v132]) { Ok(v) => v, Err(e) => return Err(e) };
let v134 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v135 = match eo__24re_5fflatten(s, v134, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v136 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v137 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v138 = match s.apply(v136, v137) { Ok(v) => v, Err(e) => return Err(e) };
more_173_eo__24str_5fre_5fconsume(s, v135, v138, a0, v133, v128, a1, v127, v70, v126)
}
pub(super) fn more_171_eo__24str_5fre_5fconsume(s: &mut Store, v90: Term, v72: Term, a1: Term, a0: Term, v71: Term, v70: Term) -> CheckResult<Term> {
let v91 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v92 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v93 = match s.apply(v91, v92) { Ok(v) => v, Err(e) => return Err(e) };
let v94 = match s.builtin_core(EvalOp::Eq, &[v90, v93]) { Ok(v) => v, Err(e) => return Err(e) };
let v95 = match s.builtin_core(EvalOp::Not, &[v94]) { Ok(v) => v, Err(e) => return Err(e) };
let v96 = match s.builtin_core(EvalOp::And, &[v72, v95]) { Ok(v) => v, Err(e) => return Err(e) };
let v121 = match if_137_eo__24str_5fre_5fconsume(s, v96, a1, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v122 = match eo__24re_5fflatten(s, v71, v121) { Ok(v) => v, Err(e) => return Err(e) };
let v123 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v124 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v125 = match s.apply(v123, v124) { Ok(v) => v, Err(e) => return Err(e) };
let v126 = match eo__24re_5frev_5fmap_5frev(s, v122, v125) { Ok(v) => v, Err(e) => return Err(e) };
more_172_eo__24str_5fre_5fconsume(s, a0, a1, v70, v126)
}
pub(super) fn more_170_eo__24str_5fre_5fconsume(s: &mut Store, v78: Term, a1: Term, a0: Term, v77: Term, v72: Term, v71: Term, v70: Term) -> CheckResult<Term> {
let v79 = match eo__24re_5fflatten(s, v78, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v80 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v81 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v82 = match s.apply(v80, v81) { Ok(v) => v, Err(e) => return Err(e) };
let v83 = match eo__24re_5frev_5fmap_5frev(s, v79, v82) { Ok(v) => v, Err(e) => return Err(e) };
let v84 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v85 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v86 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v85, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v87 = match eo__24str_5fflatten(s, v86) { Ok(v) => v, Err(e) => return Err(e) };
let v88 = match s.builtin_list(EvalOp::ListRev, &[v84, v87]) { Ok(v) => v, Err(e) => return Err(e) };
let v89 = match eo__24str_5fre_5fconsume_5frec(s, v77, v83, v88) { Ok(v) => v, Err(e) => return Err(e) };
let v90 = match eo__24str_5fmembership_5fre(s, v89) { Ok(v) => v, Err(e) => return Err(e) };
more_171_eo__24str_5fre_5fconsume(s, v90, v72, a1, a0, v71, v70)
}
pub(super) fn more_169_eo__24str_5fre_5fconsume(s: &mut Store, v43: Term, v21: Term, a0: Term, a1: Term, v20: Term) -> CheckResult<Term> {
let v44 = match s.builtin_core(EvalOp::Not, &[v43]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_core(EvalOp::And, &[v21, v44]) { Ok(v) => v, Err(e) => return Err(e) };
let v69 = match if_135_eo__24str_5fre_5fconsume(s, v45, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v70 = match s.builtin_list(EvalOp::ListRev, &[v20, v69]) { Ok(v) => v, Err(e) => return Err(e) };
let v71 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v72 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v73 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v74 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v75 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v74, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v76 = match eo__24str_5fflatten(s, v75) { Ok(v) => v, Err(e) => return Err(e) };
let v77 = match s.builtin_list(EvalOp::ListRev, &[v73, v76]) { Ok(v) => v, Err(e) => return Err(e) };
let v78 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
more_170_eo__24str_5fre_5fconsume(s, v78, a1, a0, v77, v72, v71, v70)
}
pub(super) fn more_168_eo__24str_5fre_5fconsume(s: &mut Store, v28: Term, v31: Term, a0: Term, v26: Term, v21: Term, a1: Term, v20: Term) -> CheckResult<Term> {
let v32 = match eo__24re_5frev_5fmap_5frev(s, v28, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v34, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24str_5fflatten(s, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.builtin_list(EvalOp::ListRev, &[v33, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24str_5fre_5fconsume_5frec(s, v26, v32, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match eo__24str_5fmembership_5fre(s, v38) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v40, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_core(EvalOp::Eq, &[v39, v42]) { Ok(v) => v, Err(e) => return Err(e) };
more_169_eo__24str_5fre_5fconsume(s, v43, v21, a0, a1, v20)
}
pub(super) fn if_175_eo__24str_5fre_5fconsume(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v23, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24str_5fflatten(s, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_list(EvalOp::ListRev, &[v22, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24re_5fflatten(s, v27, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v29, v30) { Ok(v) => v, Err(e) => return Err(e) };
more_168_eo__24str_5fre_5fconsume(s, v28, v31, a0, v26, v21, a1, v20)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_176_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, v11: Term, v4: Term, v10: Term, a1: Term) -> CheckResult<Option<Term>> {
let v12 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v12, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24str_5fflatten(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_list(EvalOp::ListRev, &[v11, v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24str_5fre_5fconsume_5frec(s, v4, v10, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Eq, &[v16, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v513 = match if_175_eo__24str_5fre_5fconsume(s, v18, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v513))
}
pub(super) fn case_1_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v1, a0]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match eo__24str_5fflatten(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v4 = match s.builtin_list(EvalOp::ListRev, &[v0, v3]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match eo__24re_5fflatten(s, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v7, v8) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match eo__24re_5frev_5fmap_5frev(s, v6, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_176_eo__24str_5fre_5fconsume(s, a0, v11, v4, v10, a1)
}
pub(super) fn body_eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fconsume(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fre_5fconsume(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$str_re_consume"
pub fn eo__24str_5fre_5fconsume(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24str_5fre_5fconsume(s, a0, a1);
s.leave();
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match eo__24str_5fre_5fconsume(s, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s, v14, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v21))
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-consume"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s, a0);
s.leave();
result
}
pub(super) fn case_112_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5fconsume, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2din_2dre_2dconsume(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fre_2dloop_2delim(s: &mut Store, v26: Term, v2: Term, v11: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v26 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v26) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v27 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo_re_2eloop, &[v11, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v27, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
pub(super) fn case_0_eo__24str_5fmk_5fre_5floop_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo__40_40TypedList_2enil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.construct(Constructor::eo_Int, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListSingletonElim, &[v6, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v8, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
// EO program "$str_mk_re_loop_elim_rec"
pub fn eo__24str_5fmk_5fre_5floop_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2];
match s.cached_program(ProgramId(1072), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fmk_5fre_5floop_5felim_5frec(s, a0, a1, a2);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1072), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fmk_5fre_5floop_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fmk_5fre_5floop_5felim_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmk_5fre_5floop_5felim_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24str_5fmk_5fre_5floop_5felim_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_list(EvalOp::ListSingletonElim, &[v9, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v8, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a1) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24str_5fmk_5fre_5floop_5felim_5frec(s, v13, a2, v2, a1, v11)
}
pub(super) fn more_0_eo__24str_5fmk_5fre_5floop_5felim_5frec(s: &mut Store, v13: Term, a2: Term, v2: Term, a1: Term, v11: Term) -> CheckResult<Option<Term>> {
let v14 = match s.apply(v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match eo__24str_5fmk_5fre_5floop_5felim_5frec(s, v2, a1, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v11, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v16))
}
pub(super) fn requires_1_eo__24eo_5fprog_5fre_2dloop_2delim(s: &mut Store, v15: Term, v16: Term, v11: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v15 != v16 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v15) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo__40_40TypedList_2econs, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.builtin_core(EvalOp::Neg, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Add, &[v20, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_list(EvalOp::ListRepeat, &[v18, v19, v21]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_list(EvalOp::ListRepeat, &[v23, v9, v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match eo__24str_5fmk_5fre_5floop_5felim_5frec(s, v22, v9, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_list(EvalOp::ListSingletonElim, &[v17, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match requires_0_eo__24eo_5fprog_5fre_2dloop_2delim(s, v26, v2, v11, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dloop_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v10 = match s.destruct(Constructor::eo_re_2eloop, v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some(fields) = v10 else { return Ok(None); }
;
let v11 = fields[0];
let v12 = fields[1];
let v13 = match s.builtin_core(EvalOp::Neg, &[v11]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.builtin_core(EvalOp::Add, &[v13, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match requires_1_eo__24eo_5fprog_5fre_2dloop_2delim(s, v15, v16, v11, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v33))
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dloop_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dloop_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-loop-elim"
pub fn eo__24eo_5fprog_5fre_2dloop_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dloop_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_113_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5floop_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2dloop_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, v2: Term, v50: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v2 != v50 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v51 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v52, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v53, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.apply(v51, v54) { Ok(v) => v, Err(e) => return Err(e) };
let v56 = match s.apply(v55, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v56)
}
pub(super) fn more_2_eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, v43: Term, v42: Term, v41: Term, v9: Term, v40: Term, v30: Term, v2: Term, v12: Term) -> CheckResult<Term> {
let v44 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v43, v44) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.construct(Constructor::eo__24emb_5fVar, &[v42, v45]) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.apply(v41, v46) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v47, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v40, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v30, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match requires_0_eo__24eo_5fprog_5fre_2deq_2delim(s, v2, v50, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, v12: Term, v31: Term, v9: Term, v30: Term, v2: Term) -> CheckResult<Term> {
let v32 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,114,101,95,101,113,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v34, v35) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.construct(Constructor::eo__24emb_5fVar, &[v33, v36]) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v32, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.apply(v38, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v31, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,114,101,95,101,113,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_2_eo__24eo_5fprog_5fre_2deq_2delim(s, v43, v42, v41, v9, v40, v30, v2, v12)
}
pub(super) fn requires_3_eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, v18: Term, v19: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.construct(Constructor::eo_forall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo__24eo_5fList_5fcons, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Str(EoString::from_code_points(vec![64,118,97,114,46,114,101,95,101,113,]))) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_Seq, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.construct(Constructor::eo_Char, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v23, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.construct(Constructor::eo__24emb_5fVar, &[v22, v25]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v21, v26) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v27, v28) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.apply(v20, v29) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2deq_2delim(s, v12, v31, v9, v30, v2)
}
pub(super) fn more_4_eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, v16: Term, v17: Term, v12: Term, v9: Term, v2: Term) -> CheckResult<Option<Term>> {
let v18 = match eo__24is_5fclosed_5frec(s, v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match requires_3_eo__24eo_5fprog_5fre_2deq_2delim(s, v18, v19, v12, v9, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v58))
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.apply(v14, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.construct(Constructor::eo__24eo_5fList_5fnil, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fre_2deq_2delim(s, v16, v17, v12, v9, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2deq_2delim(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-eq-elim"
pub fn eo__24eo_5fprog_5fre_2deq_2delim(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2deq_2delim(s, a0);
s.leave();
result
}
pub(super) fn case_114_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5feq_5felim, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2deq_2delim(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, v4: Term, v5: Term, v2: Term, a0: Term) -> CheckResult<Term> {
if v4 != v5 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v4) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.builtin_list(EvalOp::ListSingletonIntro, &[v6, v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match eo__24str_5fflatten(s, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match eo__24str_5feval_5fstr_5fin_5fre_5frec(s, v8, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
pub(super) fn case_0_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.builtin_core(EvalOp::IsStr, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match requires_0_eo__24str_5fre_5fincludes_5fbase_5frec(s, v4, v5, v2, a0) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v10))
}
pub(super) fn case_1_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v4))
}
pub(super) fn if_1_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, condition: Term, v2: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
Some(false) => {
let v30 = match s.builtin_core(EvalOp::ToInt, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::ToInt, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.builtin_core(EvalOp::Gt, &[v30, v31]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, condition: Term, v12: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v37 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v37)
}
Some(false) => {
let v38 = match s.builtin_core(EvalOp::ToInt, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.builtin_core(EvalOp::Gt, &[v38, v39]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v40)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, condition: Term, v2: Term, v9: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v46 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v46)
}
Some(false) => {
let v47 = match s.builtin_core(EvalOp::ToInt, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.builtin_core(EvalOp::Gt, &[v47, v48]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v49)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, condition: Term, v9: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v55 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v55)
}
Some(false) => {
let v56 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.builtin_core(EvalOp::Gt, &[v56, v57]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v58)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, v45: Term, v2: Term, v9: Term, v42: Term, v5: Term) -> CheckResult<Term> {
let v50 = match if_3_eo__24str_5fre_5fincludes_5fbase_5frec(s, v45, v2, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.builtin_core(EvalOp::And, &[v42, v50]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.builtin_core(EvalOp::Eq, &[v52, v53]) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match if_4_eo__24str_5fre_5fincludes_5fbase_5frec(s, v54, v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match s.builtin_core(EvalOp::And, &[v51, v59]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v60)
}
pub(super) fn requires_6_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, v24: Term, v25: Term, v2: Term, v12: Term, v5: Term, v9: Term) -> CheckResult<Term> {
if v24 != v25 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v24) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v26 = match s.builtin_core(EvalOp::ToInt, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.builtin_core(EvalOp::ToInt, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.builtin_core(EvalOp::Eq, &[v26, v27]) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match if_1_eo__24str_5fre_5fincludes_5fbase_5frec(s, v28, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.builtin_core(EvalOp::ToInt, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.builtin_core(EvalOp::Eq, &[v34, v35]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match if_2_eo__24str_5fre_5fincludes_5fbase_5frec(s, v36, v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.builtin_core(EvalOp::And, &[v33, v41]) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_core(EvalOp::ToInt, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.builtin_core(EvalOp::Eq, &[v43, v44]) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24str_5fre_5fincludes_5fbase_5frec(s, v45, v2, v9, v42, v5)
}
pub(super) fn requires_7_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, v21: Term, v22: Term, v9: Term, v2: Term, v12: Term, v5: Term) -> CheckResult<Term> {
if v21 != v22 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v21) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v23 = match s.builtin_core(EvalOp::ToInt, &[v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.builtin_core(EvalOp::IsNeg, &[v23]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v61 = match requires_6_eo__24str_5fre_5fincludes_5fbase_5frec(s, v24, v25, v2, v12, v5, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v61)
}
pub(super) fn requires_8_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, v18: Term, v19: Term, v12: Term, v9: Term, v2: Term, v5: Term) -> CheckResult<Term> {
if v18 != v19 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v18) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.builtin_core(EvalOp::ToInt, &[v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::IsNeg, &[v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v62 = match requires_7_eo__24str_5fre_5fincludes_5fbase_5frec(s, v21, v22, v9, v2, v12, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v62)
}
pub(super) fn requires_9_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, v15: Term, v16: Term, v2: Term, v12: Term, v9: Term, v5: Term) -> CheckResult<Term> {
if v15 != v16 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v15) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.builtin_core(EvalOp::ToInt, &[v2]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::IsNeg, &[v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v63 = match requires_8_eo__24str_5fre_5fincludes_5fbase_5frec(s, v18, v19, v12, v9, v2, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v63)
}
pub(super) fn case_2_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_re_2erange, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.builtin_core(EvalOp::ToInt, &[v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.builtin_core(EvalOp::IsNeg, &[v14]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v64 = match requires_9_eo__24str_5fre_5fincludes_5fbase_5frec(s, v15, v16, v2, v12, v9, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v64))
}
pub(super) fn if_10_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_0_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, v14: Term) -> CheckResult<Option<Term>> {
let v16 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v14 != v16 { return Ok(None); }
let v17 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v17))
}
pub(super) fn case_0_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.unapply(v5) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.unapply(v6) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v13 != v15 { return Ok(None); }
more_0_eo__24str_5fre_5fincludes_5flhs_5fstar(s, v14)
}
pub(super) fn case_3_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn case_1_eo__24str_5fre_5fincludes_5frhs_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn case_1_eo__24str_5fre_5fincludes_5flhs_5funion(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
pub(super) fn more_0_eo__24re_5fis_5funbound_5fwildcard(s: &mut Store, v16: Term, v18: Term, v13: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
if v16 != v18 { return Ok(None); }
let v19 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v24)))
}
pub(super) fn case_0_eo__24re_5fis_5funbound_5fwildcard(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
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
let v10 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v12, v13)) = v11 else { return Ok(None); }
;
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_0_eo__24re_5fis_5funbound_5fwildcard(s, v16, v18, v13)
}
pub(super) fn case_1_eo__24re_5fis_5funbound_5fwildcard(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
Ok(Some(Next::Again([v2])))
}
pub(super) fn case_2_eo__24re_5fis_5funbound_5fwildcard(s: &mut Store, a0: Term) -> CheckResult<Option<Next<[Term; 1]>>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v0)))
}
pub(super) fn step_eo__24re_5fis_5funbound_5fwildcard(s: &mut Store, a0: Term) -> CheckResult<Next<[Term; 1]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24re_5fis_5funbound_5fwildcard(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24re_5fis_5funbound_5fwildcard(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24re_5fis_5funbound_5fwildcard(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24re_5fis_5funbound_5fwildcard(s: &mut Store, mut a0: Term) -> CheckResult<Term> {
loop {
match step_eo__24re_5fis_5funbound_5fwildcard(s, a0) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
}
Err(e) => return Err(e),
}
}
}
// EO program "$re_is_unbound_wildcard"
pub fn eo__24re_5fis_5funbound_5fwildcard(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0];
match s.cached_program(ProgramId(965), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24re_5fis_5funbound_5fwildcard(s, a0);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(965), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn if_8_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v56 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v56)
}
Some(false) => {
let v57 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v57)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_7_eo__24str_5fre_5fincludes_5frec(s: &mut Store, v13: Term, v14: Term, v12: Term, v5: Term, v2: Term) -> CheckResult<Option<Term>> {
let v15 = match s.apply(v13, v14) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.apply(v16, v17) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v15, v18) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v12, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.builtin_core(EvalOp::Eq, &[v5, v20]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v22, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.builtin_core(EvalOp::Eq, &[v2, v24]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.builtin_core(EvalOp::And, &[v21, v25]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v26))
}
pub(super) fn case_5_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_7_eo__24str_5fre_5fincludes_5frec(s, v13, v14, v12, v5, v2)
}
pub(super) fn case_6_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v0))
}
// EO program "$str_re_includes_base_rec"
pub fn eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1083), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fincludes_5fbase_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1083), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fincludes_5fbase_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fre_5fincludes_5fbase_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fre_5fincludes_5fbase_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24str_5fre_5fincludes_5fbase_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_3_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match eo__24str_5fre_5fincludes_5flhs_5funion(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v2 = match s.builtin_core(EvalOp::Eq, &[v0, v1]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_12_eo__24str_5fre_5fincludes_5fbase_5frec(s, v2, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn if_11_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v7 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match eo__24str_5fre_5fincludes_5flhs_5fstar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.builtin_core(EvalOp::Eq, &[v8, v9]) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_10_eo__24str_5fre_5fincludes_5fbase_5frec(s, v10) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_12_eo__24str_5fre_5fincludes_5fbase_5frec(s: &mut Store, condition: Term, a0: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v3 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v3)
}
Some(false) => {
let v4 = match eo__24str_5fre_5fincludes_5frhs_5finter(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Eq, &[v4, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match if_11_eo__24str_5fre_5fincludes_5fbase_5frec(s, v6, a0, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
// EO program "$str_re_includes_concat"
pub fn eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(1084), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fincludes_5fconcat(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1084), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(s.stuck()); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fincludes_5fconcat(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.builtin_core(EvalOp::Eq, &[a0, a2]) { Ok(v) => v, Err(e) => return Err(e) };
let v3 = match if_0_eo__24str_5fre_5fincludes_5fconcat(s, v0, a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match if_2_eo__24str_5fre_5fincludes_5fconcat(s, v3, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v60 = match if_10_eo__24str_5fre_5fincludes_5fconcat(s, v9, a0, a1, a3, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v60))
}
pub(super) fn if_0_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a0: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v1)
}
Some(false) => {
let v2 = match eo__24str_5fre_5fincludes_5fbase_5frec(s, a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v2)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a1: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match eo__24str_5fre_5fincludes_5frec(s, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a1: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v4 = match s.builtin_core(EvalOp::Eq, &[a1, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_1_eo__24str_5fre_5fincludes_5fconcat(s, v4, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v7)
}
Some(false) => {
let v8 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a0: Term, a1: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v24 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v24)
}
Some(false) => {
let v25 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24str_5fre_5fincludes_5frec(s, v27, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v28)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a0: Term, a1: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v19 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v19)
}
Some(false) => {
let v20 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.builtin_core(EvalOp::Eq, &[v22, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match if_3_eo__24str_5fre_5fincludes_5fconcat(s, v23, a0, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_5_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a0: Term, a1: Term, a3: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v15 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v15, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match s.apply(v16, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.builtin_core(EvalOp::Eq, &[v17, a3]) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match if_4_eo__24str_5fre_5fincludes_5fconcat(s, v18, a0, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v30)
}
Some(false) => {
let v31 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v31)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_6_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a2: Term, a3: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v48 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v48)
}
Some(false) => {
let v49 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v49, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.apply(v50, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match eo__24str_5fre_5fincludes_5frec(s, a1, v51) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v52)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_7_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a2: Term, a3: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v44 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.builtin_core(EvalOp::Eq, &[a1, v46]) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match if_6_eo__24str_5fre_5fincludes_5fconcat(s, v47, a2, a3, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v53)
}
Some(false) => {
let v54 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v54)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_9_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a0: Term, a2: Term, a3: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v33 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
Some(false) => {
let v34 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v35, v36) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v38, v39) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v37, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v34, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.builtin_core(EvalOp::Eq, &[a0, v42]) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match if_7_eo__24str_5fre_5fincludes_5fconcat(s, v43, a2, a3, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match if_8_eo__24str_5fre_5fincludes_5fconcat(s, v55) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v58)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_10_eo__24str_5fre_5fincludes_5fconcat(s: &mut Store, condition: Term, a0: Term, a1: Term, a3: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v10 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
Some(false) => {
let v11 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match eo__24re_5fis_5funbound_5fwildcard(s, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match if_5_eo__24str_5fre_5fincludes_5fconcat(s, v14, a0, a1, a3) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match if_9_eo__24str_5fre_5fincludes_5fconcat(s, v32, a0, a2, a3, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v59)
}
None => Ok(s.stuck()),
}
}
// EO program "$str_re_includes_lhs_star"
pub fn eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1085), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fincludes_5flhs_5fstar(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1085), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fincludes_5flhs_5fstar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fre_5fincludes_5flhs_5fstar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fre_5fincludes_5flhs_5fstar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_3_eo__24str_5fre_5fincludes_5flhs_5fstar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_1_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v5, v6)) = v4 else { return Ok(None); }
;
let v7 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.builtin_core(EvalOp::Eq, &[v2, v6]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match if_1_eo__24str_5fre_5fincludes_5flhs_5fstar(s, v8, v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v11))
}
pub(super) fn case_2_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.builtin_core(EvalOp::Eq, &[v2, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match if_2_eo__24str_5fre_5fincludes_5flhs_5fstar(s, v4, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v7))
}
pub(super) fn if_1_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, condition: Term, v2: Term, v6: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v9 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match eo__24str_5fre_5fincludes_5frec(s, v2, v6) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v10)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_2_eo__24str_5fre_5fincludes_5flhs_5fstar(s: &mut Store, condition: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v5)
}
Some(false) => {
let v6 = match eo__24str_5fre_5fincludes_5frec(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v6)
}
None => Ok(s.stuck()),
}
}
// EO program "$str_re_includes_lhs_union"
pub fn eo__24str_5fre_5fincludes_5flhs_5funion(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1086), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fincludes_5flhs_5funion(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1086), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fincludes_5flhs_5funion(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fincludes_5flhs_5funion(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fre_5fincludes_5flhs_5funion(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fre_5fincludes_5flhs_5funion(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::Eq, &[v5, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24str_5fre_5fincludes_5flhs_5funion(s, v7, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_1_eo__24str_5fre_5fincludes_5flhs_5funion(s, v10, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn if_0_eo__24str_5fre_5fincludes_5flhs_5funion(s: &mut Store, condition: Term, v5: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match eo__24str_5fre_5fincludes_5frec(s, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5fre_5fincludes_5flhs_5funion(s: &mut Store, condition: Term, v2: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match eo__24str_5fre_5fincludes_5flhs_5funion(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
// EO program "$str_re_includes_rec"
pub fn eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1087), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fincludes_5frec(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1087), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match cases_0_0_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match cases_0_1_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v13, v14)) = v12 else { return Ok(None); }
;
let v15 = match s.unapply(v13) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v16, v17)) = v15 else { return Ok(None); }
;
let v18 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24str_5fre_5fincludes_5frec(s, v16, v18, v14, v5, v17)
}
pub(super) fn case_1_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.builtin_core(EvalOp::Eq, &[v5, a1]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_2_eo__24str_5fre_5fincludes_5frec(s, v12, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_2_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v15 != v17 { return Ok(None); }
let v18 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
more_5_eo__24str_5fre_5fincludes_5frec(s, v16, v18, v5, v2, v12)
}
pub(super) fn case_3_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.builtin_core(EvalOp::Eq, &[a0, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match if_6_eo__24str_5fre_5fincludes_5frec(s, v12, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v15))
}
pub(super) fn case_4_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v8, v9)) = v7 else { return Ok(None); }
;
let v10 = match s.unapply(v8) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v11, v12)) = v10 else { return Ok(None); }
;
let v13 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match eo__24str_5fre_5fincludes_5fconcat(s, v5, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v14))
}
pub(super) fn cases_0_0_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_0_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_1_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_2_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_3_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn cases_0_1_eo__24str_5fre_5fincludes_5frec(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_4_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_5_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_6_eo__24str_5fre_5fincludes_5frec(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24str_5fre_5fincludes_5frec(s: &mut Store, condition: Term, v5: Term, v17: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v25 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v25)
}
Some(false) => {
let v26 = match eo__24str_5fre_5fincludes_5fbase_5frec(s, v5, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v26)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24str_5fre_5fincludes_5frec(s: &mut Store, v16: Term, v18: Term, v14: Term, v5: Term, v17: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
let v19 = match s.unapply(v14) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v20, v21)) = v19 else { return Ok(None); }
;
let v22 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v20 != v22 { return Ok(None); }
let v23 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v21 != v23 { return Ok(None); }
let v24 = match s.builtin_core(EvalOp::Eq, &[v5, v17]) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match if_0_eo__24str_5fre_5fincludes_5frec(s, v24, v5, v17) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v27))
}
pub(super) fn if_2_eo__24str_5fre_5fincludes_5frec(s: &mut Store, condition: Term, v5: Term, a1: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match eo__24str_5fre_5fincludes_5fbase_5frec(s, v5, a1) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_3_eo__24str_5fre_5fincludes_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v23 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v23)
}
Some(false) => {
let v24 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v24, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v25, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match eo__24str_5fre_5fincludes_5fbase_5frec(s, v26, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_4_eo__24str_5fre_5fincludes_5frec(s: &mut Store, condition: Term, v5: Term, v2: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v29 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v29)
}
Some(false) => {
let v30 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match s.apply(v30, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v33 = match eo__24str_5fre_5fincludes_5fconcat(s, v5, v2, v12, v32) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v33)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_5_eo__24str_5fre_5fincludes_5frec(s: &mut Store, v16: Term, v18: Term, v5: Term, v2: Term, v12: Term) -> CheckResult<Option<Term>> {
if v16 != v18 { return Ok(None); }
let v19 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v20, v2) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.builtin_core(EvalOp::Eq, &[v21, v12]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match if_3_eo__24str_5fre_5fincludes_5frec(s, v22, v5, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match if_4_eo__24str_5fre_5fincludes_5frec(s, v28, v5, v2, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v34))
}
pub(super) fn if_6_eo__24str_5fre_5fincludes_5frec(s: &mut Store, condition: Term, a0: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v13 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v13)
}
Some(false) => {
let v14 = match eo__24str_5fre_5fincludes_5fbase_5frec(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
// EO program "$str_re_includes_rhs_inter"
pub fn eo__24str_5fre_5fincludes_5frhs_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1088), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fre_5fincludes_5frhs_5finter(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1088), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fre_5fincludes_5frhs_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fre_5fincludes_5frhs_5finter(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fre_5fincludes_5frhs_5finter(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fre_5fincludes_5frhs_5finter(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.builtin_core(EvalOp::Eq, &[a0, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match if_0_eo__24str_5fre_5fincludes_5frhs_5finter(s, v7, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match if_1_eo__24str_5fre_5fincludes_5frhs_5finter(s, v10, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn if_0_eo__24str_5fre_5fincludes_5frhs_5finter(s: &mut Store, condition: Term, a0: Term, v5: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v8 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v8)
}
Some(false) => {
let v9 = match eo__24str_5fre_5fincludes_5frec(s, a0, v5) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_1_eo__24str_5fre_5fincludes_5frhs_5finter(s: &mut Store, condition: Term, a0: Term, v2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v11 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v11)
}
Some(false) => {
let v12 = match eo__24str_5fre_5fincludes_5frhs_5finter(s, a0, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v12)
}
None => Ok(s.stuck()),
}
}
pub(super) fn if_0_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, condition: Term, v23: Term, v12: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v32 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v32)
}
Some(false) => {
let v33 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24re_5fflatten(s, v33, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match eo__24re_5fflatten(s, v35, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match eo__24str_5fre_5fincludes_5frec(s, v34, v36) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v37)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, v50: Term, v51: Term) -> CheckResult<Term> {
let v52 = match s.apply(v50, v51) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v52)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, v38: Term, v39: Term, v12: Term, v23: Term) -> CheckResult<Term> {
if v38 != v39 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v38) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v40 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v41, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.apply(v44, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v43, v45) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.apply(v46, v47) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v42, v48) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v40, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, v50, v51)
}
pub(super) fn more_4_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, v31: Term, v23: Term, v12: Term) -> CheckResult<Option<Term>> {
let v38 = match if_0_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, v31, v23, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match requires_2_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, v38, v39, v12, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v53))
}
pub(super) fn more_3_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, v19: Term, v16: Term, v2: Term, v12: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo_re_2eall, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v25 { return Ok(None); }
let v26 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v26 { return Ok(None); }
let v27 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match eo__24re_5fflatten(s, v27, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match eo__24re_5fflatten(s, v29, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.builtin_core(EvalOp::Eq, &[v28, v30]) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, v31, v23, v12)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_re_2einter, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_3_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, v19, v16, v2, v12)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-inter-inclusion"
pub fn eo__24eo_5fprog_5fre_2dinter_2dinclusion(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, a0);
s.leave();
result
}
pub(super) fn case_115_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5finter_5finclusion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2dinter_2dinclusion(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn cases_0_28_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
if let Some(found) = match case_112_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_113_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_114_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
if let Some(found) = match case_115_eo__24eo_5fcmd_5fstep_5fproven(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(Some(found)); }
Ok(None)
}
pub(super) fn if_0_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, condition: Term, v12: Term, v23: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v36 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v36)
}
Some(false) => {
let v37 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match eo__24re_5fflatten(s, v37, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match eo__24re_5fflatten(s, v39, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match eo__24str_5fre_5fincludes_5frec(s, v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v41)
}
None => Ok(s.stuck()),
}
}
pub(super) fn more_1_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, v55: Term, v54: Term) -> CheckResult<Term> {
let v56 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v57 = match s.apply(v55, v56) { Ok(v) => v, Err(e) => return Err(e) };
let v58 = match s.apply(v54, v57) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v58)
}
pub(super) fn requires_2_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, v42: Term, v43: Term, v12: Term, v23: Term) -> CheckResult<Term> {
if v42 != v43 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v42) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v44 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v46 = match s.apply(v45, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v47 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v48 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v49 = match s.apply(v48, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v50 = match s.apply(v47, v49) { Ok(v) => v, Err(e) => return Err(e) };
let v51 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v52 = match s.apply(v50, v51) { Ok(v) => v, Err(e) => return Err(e) };
let v53 = match s.apply(v46, v52) { Ok(v) => v, Err(e) => return Err(e) };
let v54 = match s.apply(v44, v53) { Ok(v) => v, Err(e) => return Err(e) };
let v55 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
more_1_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, v55, v54)
}
pub(super) fn more_4_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, v23: Term, v32: Term, v12: Term) -> CheckResult<Option<Term>> {
let v33 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match eo__24re_5fflatten(s, v33, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.builtin_core(EvalOp::Eq, &[v32, v34]) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match if_0_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, v35, v12, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v59 = match requires_2_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, v42, v43, v12, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v59))
}
pub(super) fn more_3_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, v19: Term, v16: Term, v2: Term, v12: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v19) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo_re_2ecomp, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
let v25 = match s.construct(Constructor::eo_re_2enone, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v16 != v25 { return Ok(None); }
let v26 = match s.unapply(v2) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v27, v28)) = v26 else { return Ok(None); }
;
let v29 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v27 != v29 { return Ok(None); }
let v30 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v28 != v30 { return Ok(None); }
let v31 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24re_5fflatten(s, v31, v12) { Ok(v) => v, Err(e) => return Err(e) };
more_4_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, v23, v32, v12)
}
pub(super) fn case_0_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v13 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v11 != v13 { return Ok(None); }
let v14 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_re_2eunion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_3_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, v19, v16, v2, v12)
}
pub(super) fn body_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_re-union-inclusion"
pub fn eo__24eo_5fprog_5fre_2dunion_2dinclusion(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, a0);
s.leave();
result
}
pub(super) fn case_116_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2ere_5funion_5finclusion, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fre_2dunion_2dinclusion(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s: &mut Store, v32: Term, v2: Term, v19: Term, v16: Term, v23: Term) -> CheckResult<Term> {
if v32 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v32) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v33 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v34 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v35 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v36 = match s.apply(v35, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v37 = match s.apply(v36, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v38 = match s.apply(v34, v37) { Ok(v) => v, Err(e) => return Err(e) };
let v39 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v40 = match s.apply(v39, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v41 = match s.apply(v38, v40) { Ok(v) => v, Err(e) => return Err(e) };
let v42 = match s.apply(v33, v41) { Ok(v) => v, Err(e) => return Err(e) };
let v43 = match s.apply(v42, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v43)
}
pub(super) fn case_1_eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if a0 != v0 { return Ok(None); }
let v1 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v1))
}
// EO program "$str_mk_str_in_re_concat_star_char"
pub fn eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1];
match s.cached_program(ProgramId(1073), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s, a0, a1);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1073), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn body_eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s, a0, a1) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
pub(super) fn case_0_eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s: &mut Store, a0: Term, a1: Term) -> CheckResult<Option<Term>> {
let v0 = match s.unapply(a0) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_and, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, v5) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.apply(v9, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v7, v10) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s, v2, a1) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v11, v12) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v13))
}
pub(super) fn requires_1_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s: &mut Store, v25: Term, v26: Term, v19: Term, v16: Term, v23: Term, v2: Term) -> CheckResult<Term> {
if v25 != v26 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v25) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v27 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v28 = match s.apply(v27, v19) { Ok(v) => v, Err(e) => return Err(e) };
let v29 = match s.apply(v28, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v30 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v31 = match s.apply(v30, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v32 = match eo__24str_5fmk_5fstr_5fin_5fre_5fconcat_5fstar_5fchar(s, v29, v31) { Ok(v) => v, Err(e) => return Err(e) };
let v44 = match requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s, v32, v2, v19, v16, v23) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v44)
}
pub(super) fn more_2_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s: &mut Store, v9: Term, v19: Term, v16: Term, v2: Term) -> CheckResult<Option<Term>> {
let v21 = match s.unapply(v9) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v22, v23)) = v21 else { return Ok(None); }
;
let v24 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v22 != v24 { return Ok(None); }
let v25 = match eo__24str_5ffixed_5flen_5fre(s, v23) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v45 = match requires_1_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s, v25, v26, v19, v16, v23, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v45))
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.unapply(v12) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v15, v16)) = v14 else { return Ok(None); }
;
let v17 = match s.unapply(v15) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v18, v19)) = v17 else { return Ok(None); }
;
let v20 = match s.construct(Constructor::eo_str_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v18 != v20 { return Ok(None); }
more_2_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s, v9, v19, v16, v2)
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-concat-star-char"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s, a0);
s.leave();
result
}
pub(super) fn case_117_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5fconcat_5fstar_5fchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2din_2dre_2dconcat_2dstar_2dchar(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s: &mut Store, v16: Term, v2: Term, v12: Term, v9: Term) -> CheckResult<Term> {
if v16 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v16) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v17 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v18 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v19 = match s.apply(v18, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v20 = match s.apply(v19, v9) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.apply(v17, v20) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v22)
}
pub(super) fn if_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s: &mut Store, condition: Term, a0: Term, a2: Term) -> CheckResult<Term> {
let branch = match s.boolean_value(condition, false) { Ok(v) => v, Err(e) => return Err(e) };
match branch {
Some(true) => {
let v5 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.apply(v6, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v8 = match s.apply(v5, v7) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.apply(v8, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v9)
}
Some(false) => {
let v10 = match s.construct(Constructor::eo__3e_3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v11, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v10, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v13, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v14)
}
None => Ok(s.stuck()),
}
}
pub(super) fn case_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v15 = match if_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s, a3, a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v15)))
}
pub(super) fn case_1_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[a2, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, v2, v9, a3])))
}
pub(super) fn case_2_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Next<[Term; 4]>>> {
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
let v10 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v8 != v10 { return Ok(None); }
let v11 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v9 != v11 { return Ok(None); }
let v12 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, v2, a2, v12])))
}
pub(super) fn step_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Next<[Term; 4]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
let stuck3 = match s.is_stuck(a3) { Ok(v) => v, Err(e) => return Err(e) };
if stuck3 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_2_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s, a0, a1, a2, a3) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
pub(super) fn body_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s: &mut Store, mut a0: Term, mut a1: Term, mut a2: Term, mut a3: Term) -> CheckResult<Term> {
loop {
match step_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s, a0, a1, a2, a3) {
Ok(Next::Done(value)) => return Ok(value),
Ok(Next::Again(next)) => {
a0 = next[0];
a1 = next[1];
a2 = next[2];
a3 = next[3];
}
Err(e) => return Err(e),
}
}
}
// EO program "$str_mk_str_in_re_sigma_rec"
pub fn eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let cache_args = [a0, a1, a2, a3];
match s.cached_program(ProgramId(1074), &cache_args) {
Ok(Some(value)) => { s.leave(); return Ok(value); },
Ok(None) => {},
Err(error) => { s.leave(); return Err(error); },
}
let result = body_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s, a0, a1, a2, a3);
s.leave();
if let Ok(value) = result { match s.cache_program(ProgramId(1074), &cache_args, value) { Ok(v) => v, Err(e) => return Err(e) }; }
result
}
pub(super) fn case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s: &mut Store, a0: Term) -> CheckResult<Option<Term>> {
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
let v14 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Boolean(true)) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5frec(s, v12, v9, v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s, v16, v2, v12, v9) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v23))
}
pub(super) fn body_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s: &mut Store, a0: Term) -> CheckResult<Term> {
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(s.stuck()); }
if let Some(found) = match case_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s, a0) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(s.stuck())
}
// EO program "$eo_prog_str-in-re-sigma"
pub fn eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s: &mut Store, a0: Term) -> CheckResult<Term> {
match s.enter() { Ok(v) => v, Err(e) => return Err(e) };
let result = body_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s, a0);
s.leave();
result
}
pub(super) fn case_118_eo__24eo_5fcmd_5fstep_5fproven(s: &mut Store, a0: Term, a1: Term, a2: Term, a3: Term) -> CheckResult<Option<Term>> {
let v0 = match s.construct(Constructor::eo__24emb_5fr_2estr_5fin_5fre_5fsigma, &[]) { Ok(v) => v, Err(e) => return Err(e) };
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
let v6 = match eo__24eo_5fprog_5fstr_2din_2dre_2dsigma(s, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(v6))
}
pub(super) fn requires_0_eo__24eo_5fprog_5fstr_2din_2dre_2dsigma_2dstar(s: &mut Store, v19: Term, v2: Term, v12: Term, v16: Term) -> CheckResult<Term> {
if v19 != v2 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v19) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v20 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v21 = match s.construct(Constructor::eo_str_2ein_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v22 = match s.apply(v21, v12) { Ok(v) => v, Err(e) => return Err(e) };
let v23 = match s.construct(Constructor::eo_re_2e_2a, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v24 = match s.apply(v23, v16) { Ok(v) => v, Err(e) => return Err(e) };
let v25 = match s.apply(v22, v24) { Ok(v) => v, Err(e) => return Err(e) };
let v26 = match s.apply(v20, v25) { Ok(v) => v, Err(e) => return Err(e) };
let v27 = match s.apply(v26, v2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v27)
}
pub(super) fn requires_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s: &mut Store, v6: Term, v7: Term, a0: Term, a2: Term) -> CheckResult<Term> {
if v6 != v7 { return Ok(s.stuck()); }
let stuck = match s.is_stuck(v6) { Ok(v) => v, Err(e) => return Err(e) };
if stuck { return Ok(s.stuck()); }
let v8 = match s.construct(Constructor::eo__3d, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.construct(Constructor::eo_mod, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v10 = match s.construct(Constructor::eo_str_2elen, &[]) { Ok(v) => v, Err(e) => return Err(e) };
let v11 = match s.apply(v10, a0) { Ok(v) => v, Err(e) => return Err(e) };
let v12 = match s.apply(v9, v11) { Ok(v) => v, Err(e) => return Err(e) };
let v13 = match s.apply(v12, a2) { Ok(v) => v, Err(e) => return Err(e) };
let v14 = match s.apply(v8, v13) { Ok(v) => v, Err(e) => return Err(e) };
let v15 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v16 = match s.apply(v14, v15) { Ok(v) => v, Err(e) => return Err(e) };
Ok(v16)
}
pub(super) fn case_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.construct(Constructor::eo_str_2eto_5fre, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v1 != v3 { return Ok(None); }
let v4 = match s.literal(Lit::Str(EoString::from_code_points(vec![]))) { Ok(v) => v, Err(e) => return Err(e) };
if v2 != v4 { return Ok(None); }
let v5 = match s.literal(Lit::Numeral(Integer::from(0u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v6 = match s.builtin_core(EvalOp::Eq, &[a2, v5]) { Ok(v) => v, Err(e) => return Err(e) };
let v7 = match s.literal(Lit::Boolean(false)) { Ok(v) => v, Err(e) => return Err(e) };
let v17 = match requires_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s, v6, v7, a0, a2) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Done(v17)))
}
pub(super) fn case_1_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Option<Next<[Term; 3]>>> {
let v0 = match s.unapply(a1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v1, v2)) = v0 else { return Ok(None); }
;
let v3 = match s.unapply(v1) { Ok(v) => v, Err(e) => return Err(e) };
let Some((v4, v5)) = v3 else { return Ok(None); }
;
let v6 = match s.construct(Constructor::eo_re_2e_2b_2b, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v4 != v6 { return Ok(None); }
let v7 = match s.construct(Constructor::eo_re_2eallchar, &[]) { Ok(v) => v, Err(e) => return Err(e) };
if v5 != v7 { return Ok(None); }
let v8 = match s.literal(Lit::Numeral(Integer::from(1u32))) { Ok(v) => v, Err(e) => return Err(e) };
let v9 = match s.builtin_core(EvalOp::Add, &[a2, v8]) { Ok(v) => v, Err(e) => return Err(e) };
Ok(Some(Next::Again([a0, v2, v9])))
}
pub(super) fn step_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s: &mut Store, a0: Term, a1: Term, a2: Term) -> CheckResult<Next<[Term; 3]>> {
match s.tick() { Ok(v) => v, Err(e) => return Err(e) };
let stuck0 = match s.is_stuck(a0) { Ok(v) => v, Err(e) => return Err(e) };
if stuck0 { return Ok(Next::Done(s.stuck())); }
let stuck1 = match s.is_stuck(a1) { Ok(v) => v, Err(e) => return Err(e) };
if stuck1 { return Ok(Next::Done(s.stuck())); }
let stuck2 = match s.is_stuck(a2) { Ok(v) => v, Err(e) => return Err(e) };
if stuck2 { return Ok(Next::Done(s.stuck())); }
if let Some(found) = match case_0_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
if let Some(found) = match case_1_eo__24str_5fmk_5fstr_5fin_5fre_5fsigma_5fstar_5frec(s, a0, a1, a2) { Ok(v) => v, Err(e) => return Err(e) } { return Ok(found); }
Ok(Next::Done(s.stuck()))
}
