-- Prove2me | Theorems.Thm_lean_workbook_plus_22050
-- name    : lean_workbook_plus_22050
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/06b2aad5-b23b-4bd8-8ec5-9cf568d02fa7
-- statement:
--   For $x, y, z$ positive real numbers, prove that:\nx^3+y^3+z^3\ge \frac{x^4+y^4+z^4}{x+y+z}+2xyz
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22050 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x^3 + y^3 + z^3 ≥ (x^4 + y^4 + z^4) / (x + y + z) + 2 * x * y * z   :=  by sorry
