-- Prove2me | Theorems.Thm_lean_workbook_plus_65196
-- name    : lean_workbook_plus_65196
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e8f2795b-6221-426d-9a4f-41406083bc28
-- statement:
--   Find the value of the expression: $\frac{1}{1\times2} + \frac{1}{2\times3} + \frac{1}{3\times4} + \ldots + \frac{1}{9\times10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65196 (h : ∀ n : ℕ, (1 : ℝ) / (n * (n + 1)) = (1 : ℝ) / n - (1 : ℝ) / (n + 1)) : ∑ n in Finset.Icc (1 : ℕ) 9, (1 : ℝ) / (n * (n + 1)) = (5 : ℝ) / 11   :=  by sorry
