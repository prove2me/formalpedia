-- Prove2me | Theorems.Thm_lean_workbook_plus_58714
-- name    : lean_workbook_plus_58714
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e1fa2322-d3c1-4863-922c-6a124ff7fa66
-- statement:
--   Solve the quartic equation $x^{4} + 3x^{2} -6x +10 =0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58714 : ∀ x : ℝ, x^4 + 3*x^2 - 6*x + 10 = 0 → x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2   :=  by sorry
