-- Prove2me | Theorems.Thm_lean_workbook_plus_31867
-- name    : lean_workbook_plus_31867
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/af3cead5-650d-442c-bef5-527021621c47
-- statement:
--   Find the sum of the roots of the equation $x^2 - 4x + 3 = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31867 (f : ℝ → ℝ) : f x = x^2 - 4*x + 3 → f x = 0 → x = 1 ∨ x = 3 ∧ 1 + 3 = 4   :=  by sorry
