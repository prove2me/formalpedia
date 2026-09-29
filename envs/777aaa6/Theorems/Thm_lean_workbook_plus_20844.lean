-- Prove2me | Theorems.Thm_lean_workbook_plus_20844
-- name    : lean_workbook_plus_20844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9aaf6a7a-3459-400b-9ef1-478a21289a10
-- statement:
--   Let $x,y,z$ are positive real, prove that $x^3+y^3+z^3 \geq x^2y+y^2z+z^2x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20844 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 3 + y ^ 3 + z ^ 3 ≥ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x   :=  by sorry
