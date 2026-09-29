-- Prove2me | Theorems.Thm_lean_workbook_plus_34338
-- name    : lean_workbook_plus_34338
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f87b1a3b-d395-461f-99b8-45a2e70afc7f
-- statement:
--   If $y=x^n$ and $n$ is an irrational number, is $\frac{dy}{dx}=nx^{n-1}$ true?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34338 (x : ℝ) (n : ℝ) (hn : n ≠ 0) (h : n ∉ Set.range ((↑) : ℚ → ℝ)) : ∀ y, y = x ^ n → ∀ deriv_y, deriv_y = n * x ^ (n - 1)   :=  by sorry
