-- Prove2me | Theorems.Thm_lean_workbook_plus_23117
-- name    : lean_workbook_plus_23117
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1f559bbd-50db-41d1-b63e-d89f3645f15d
-- statement:
--   For $ x,y,z>0 $ real numbers, prove that:\n$ x(y+z) + y(x+z) + z(x+y) + \frac{8xyz}{x+y+z} \ge \frac{5(x+y)(y+z)(z+x)}{x+y+z} \ \ ; $\n\nTry $z\rightarrow0^+$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23117 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * (y + z) + y * (x + z) + z * (x + y) + 8 * x * y * z / (x + y + z) ≥ 5 * (x + y) * (y + z) * (z + x) / (x + y + z)   :=  by sorry
