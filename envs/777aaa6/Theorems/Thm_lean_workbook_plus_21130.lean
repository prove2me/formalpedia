-- Prove2me | Theorems.Thm_lean_workbook_plus_21130
-- name    : lean_workbook_plus_21130
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/be9ef461-bc24-4ec1-b05c-47ff7f1fad8b
-- statement:
--   Prove that $\lim_{x \to 0} \frac{-\ln(1-x)}x =1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21130 : ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Iio δ → |(-Real.log (1 - x)) / x - 1| < ε   :=  by sorry
