-- Prove2me | Theorems.Thm_lean_workbook_plus_79422
-- name    : lean_workbook_plus_79422
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8c6b08ef-96b0-4e50-a447-6b7b1d3f1518
-- statement:
--   Doing so, we have $ 23A+23B = 12C \implies 23(A+B) = 12C \implies \frac{C}{A+B} = \frac{23}{12}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79422  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c = 1)
  (h₂ : 23 * a + 23 * b = 12 * c) :
  c / (a + b) = 23 / 12   :=  by sorry
