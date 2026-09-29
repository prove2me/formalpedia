-- Prove2me | Theorems.Thm_lean_workbook_plus_19622
-- name    : lean_workbook_plus_19622
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c5ad4daa-4f87-4e8e-87df-26fe0e9cd69d
-- statement:
--   If $x,y,z>0$ , prove that $(3x+y)(3y+z)(3z+x) \ge 64xyz$ . When we have equality;
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19622 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (3*x+y)*(3*y+z)*(3*z+x) ≥ 64*x*y*z   :=  by sorry
