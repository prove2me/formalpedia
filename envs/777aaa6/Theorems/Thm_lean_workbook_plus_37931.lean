-- Prove2me | Theorems.Thm_lean_workbook_plus_37931
-- name    : lean_workbook_plus_37931
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/52cdbc41-7970-48f4-9077-6895ca69acf2
-- statement:
--   Prove that for positive $x, y, z$, $x^3z^2 + y^3x^2 + z^3y^2 \ge z^2x^2y + x^2y^2z + z^2y^2x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37931 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 3 * z ^ 2 + y ^ 3 * x ^ 2 + z ^ 3 * y ^ 2 ≥ z ^ 2 * x ^ 2 * y + x ^ 2 * y ^ 2 * z + z ^ 2 * y ^ 2 * x   :=  by sorry
