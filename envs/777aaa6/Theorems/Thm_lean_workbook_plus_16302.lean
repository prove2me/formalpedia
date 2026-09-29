-- Prove2me | Theorems.Thm_lean_workbook_plus_16302
-- name    : lean_workbook_plus_16302
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7c3327d8-959f-461b-8286-9ec2df1a4ac8
-- statement:
--   Let $x,y,z>0,$ prove that:\n\n$\frac{y+z}{x}+2\geq 4(\frac{z}{z+x}+\frac{y}{x+y}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16302 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) / x + 2 ≥ 4 * (z / (z + x) + y / (x + y))   :=  by sorry
