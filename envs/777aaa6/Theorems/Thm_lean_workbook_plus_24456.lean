-- Prove2me | Theorems.Thm_lean_workbook_plus_24456
-- name    : lean_workbook_plus_24456
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/013e403f-6dc4-4fb3-b17b-e77c3cc2f75a
-- statement:
--   Prove that $\frac{n^{2}}{n^{2}-1}=1+\frac{\frac{1}{2}}{n-1}-\frac{\frac{1}{2}}{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24456  (n : ℝ)
  (h₀ : n ≠ 1)
  (h₁ : n ≠ -1) :
  n^2 / (n^2 - 1) = 1 + 1 / (2 * (n - 1)) - 1 / (2 * (n + 1))   :=  by sorry
