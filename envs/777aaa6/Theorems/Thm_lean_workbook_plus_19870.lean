-- Prove2me | Theorems.Thm_lean_workbook_plus_19870
-- name    : lean_workbook_plus_19870
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a070fec2-1c8f-4ace-82ff-e4f8a1dd1ba3
-- statement:
--   One root of $mx^{2}-10x+3=0$ is $\frac{2}{3}$ of the other root. What is the sum of the roots?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19870 (m : ℝ) (f : ℝ → ℝ) (hf: f x = m*x^2 - 10*x + 3) : ∃ r₁ r₂, f r₁ = 0 ∧ f r₂ = 0 ∧ r₁ = (2/3)*r₂ → r₁ + r₂ = 5/4   :=  by sorry
