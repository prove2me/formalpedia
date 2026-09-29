-- Prove2me | Theorems.Thm_lean_workbook_plus_42308
-- name    : lean_workbook_plus_42308
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5c5b58cc-5379-481e-befe-641eb1c62acf
-- statement:
--   With $b=a+u,c=a+u+v,u,v\geq 0$, the inequality is equivalent to $\left( 351\,{u}^{2}+351\,uv+351\,{v}^{2} \right) {a}^{4}+ \left( 900\,{u}^{3}+1350\,{u}^{2}v+1458\,u{v}^{2}+504\,{v}^{3} \right) {a}^{3}+ \left( 972\,{u}^{4}+1944\,{u}^{3}v+2484\,{u}^{2}{v}^{2}+1512\,u{v}^{3}+378\,{v}^{4} \right) {a}^{2}+ \left( 488\,{u}^{5}+1220\,{u}^{4}v+1892\,{u}^{3}{v}^{2}+1618\,{u}^{2}{v}^{3}+778\,u{v}^{4}+160\,{v}^{5} \right) a+92\,{u}^{6}+276\,{u}^{5}v+511\,{u}^{4}{v}^{2}+562\,{u}^{3}{v}^{3}+396\,{u}^{2}{v}^{4}+161\,u{v}^{5}+27\,{v}^{6} \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42308 {a b c u v : ℝ} (ha : a ≥ 0) (hb : b = a + u) (hc : c = a + u + v) (hu : u ≥ 0) (hv : v ≥ 0) : a^4 * (351 * u^2 + 351 * u * v + 351 * v^2) + a^3 * (900 * u^3 + 1350 * u^2 * v + 1458 * u * v^2 + 504 * v^3) + a^2 * (972 * u^4 + 1944 * u^3 * v + 2484 * u^2 * v^2 + 1512 * u * v^3 + 378 * v^4) + a * (488 * u^5 + 1220 * u^4 * v + 1892 * u^3 * v^2 + 1618 * u^2 * v^3 + 778 * u * v^4 + 160 * v^5) + (92 * u^6 + 276 * u^5 * v + 511 * u^4 * v^2 + 562 * u^3 * v^3 + 396 * u^2 * v^4 + 161 * u * v^5 + 27 * v^6) ≥ 0   :=  by sorry
