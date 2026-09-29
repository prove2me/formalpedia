-- Prove2me | Theorems.Thm_lean_workbook_plus_14869
-- name    : lean_workbook_plus_14869
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0331f41a-6dfa-495f-bd1a-e5aed82c94f4
-- statement:
--   $(x_1+x_2+x_3)^2 \ge 9+ 3x_3(x_1+x_2+x_3-3)+2x_{1}x_2-2x_3^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14869 : ∀ x₁ x₂ x₃ : ℝ, (x₁ + x₂ + x₃) ^ 2 ≥ 9 + 3 * x₃ * (x₁ + x₂ + x₃ - 3) + 2 * x₁ * x₂ - 2 * x₃ ^ 2   :=  by sorry
