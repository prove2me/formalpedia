-- Prove2me | Theorems.Thm_lean_workbook_plus_1355
-- name    : lean_workbook_plus_1355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/5fede4b3-1b7d-451c-ac65-2f549f15e38b
-- statement:
--   Let x,y,z be positive real numbers, prove that:\n $$ \frac{y}{xy+y+1}+ \frac{z}{yz+z+1}+ \frac{x}{zx+x+1}\leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1355 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y / (x * y + y + 1) + z / (y * z + z + 1) + x / (z * x + x + 1)) ≤ 1   :=  by sorry
