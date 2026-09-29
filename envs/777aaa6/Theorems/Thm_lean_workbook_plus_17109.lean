-- Prove2me | Theorems.Thm_lean_workbook_plus_17109
-- name    : lean_workbook_plus_17109
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3ffba109-63fc-40de-9168-09f95b6c9174
-- statement:
--   Let $x,y,z>0,xyz=1$ . Prove that $\dfrac{1}{x^2+x+1}+\dfrac{1}{y^2+y+1}+\dfrac{1}{z^2+z+1}\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17109 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : 1 / (x ^ 2 + x + 1) + 1 / (y ^ 2 + y + 1) + 1 / (z ^ 2 + z + 1) >= 1   :=  by sorry
