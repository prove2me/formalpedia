-- Prove2me | Theorems.Thm_lean_workbook_plus_4240
-- name    : lean_workbook_plus_4240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a52179ad-f205-4bcd-a938-f3cbe6f980c7
-- statement:
--   Let $x,y,z>0$ such that $xyz=1$ . Prove that \n $\frac{x^{2}}{x^{2}+x+1}+\frac{y^{2}}{y^{2}+y+1}+\frac{z^{2}}{z^{2}+z+1}\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4240 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (habc : x * y * z = 1) : x^2 / (x^2 + x + 1) + y^2 / (y^2 + y + 1) + z^2 / (z^2 + z + 1) ≥ 1   :=  by sorry
