-- Prove2me | Theorems.Thm_lean_workbook_plus_58700
-- name    : lean_workbook_plus_58700
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e69202d8-ac6e-40e2-8932-42517c85fc7f
-- statement:
--   Prove that the equation \n\n $\ln x = 8 - 2x^{2}$ \n\n has exactly one real root.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58700 : ∃! x : ℝ, Real.log x = 8 - 2 * x ^ 2   :=  by sorry
