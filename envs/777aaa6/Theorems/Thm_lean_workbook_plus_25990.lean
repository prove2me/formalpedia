-- Prove2me | Theorems.Thm_lean_workbook_plus_25990
-- name    : lean_workbook_plus_25990
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4e5681ef-aad5-47f3-b178-40e95adf1b5f
-- statement:
--   Let $a,y,z>0$ and xyz=1. Prove that $\frac{1}{x^2+x+1}+\frac{1}{y^2+y+1}+\frac{1}{z^2+z+1}\geq1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25990 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x * y * z = 1) : 1 / (x^2 + x + 1) + 1 / (y^2 + y + 1) + 1 / (z^2 + z + 1) >= 1   :=  by sorry
