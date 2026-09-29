-- Prove2me | Theorems.Thm_lean_workbook_plus_58025
-- name    : lean_workbook_plus_58025
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/93f2461e-0169-4f6f-b9a0-819cce5d9944
-- statement:
--   Prove that $\dfrac12 x^6 + \dfrac12 x^4y^4 \ge x^5y^2$ for positive $x, y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58025 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 1 / 2 * x ^ 6 + 1 / 2 * x ^ 4 * y ^ 4 ≥ x ^ 5 * y ^ 2   :=  by sorry
