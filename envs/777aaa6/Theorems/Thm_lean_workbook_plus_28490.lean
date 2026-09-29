-- Prove2me | Theorems.Thm_lean_workbook_plus_28490
-- name    : lean_workbook_plus_28490
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/57051990-c397-4344-b455-4557af7ecd39
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that $(x^2+y^2+z^2)^2\ge3xyz(x+y+z)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28490 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x^2 + y^2 + z^2)^2 ≥ 3 * x * y * z * (x + y + z)   :=  by sorry
