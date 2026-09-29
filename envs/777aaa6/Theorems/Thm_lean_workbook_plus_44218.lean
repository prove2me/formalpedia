-- Prove2me | Theorems.Thm_lean_workbook_plus_44218
-- name    : lean_workbook_plus_44218
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b50fb5ef-72d9-4c53-9259-04e9aa3d66df
-- statement:
--   Prove that $\frac{x^2+1}{x^2-1} = \frac{x}{x+1} + \frac{1}{x-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44218  (x : ℝ)
  (h₀ : x ≠ 1)
  (h₁ : x ≠ -1) :
  (x^2 + 1) / (x^2 - 1) = x / (x + 1) + 1 / (x - 1)   :=  by sorry
