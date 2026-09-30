-- Prove2me | solution 1 for lean_workbook_plus_3454
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:53:35.824773+00:00
-- url     : https://prove2.me/submissions/fef0fbd7-c4bb-4c01-b8a9-21a94a60878c

import Mathlib.Analysis.Complex.Basic

theorem solution : ∀ x₁ x₂ : ℝ, (1 - x₁) * (1 - x₂) ≥ 1 - x₁ - x₂ + x₁ * x₂ := by
  intro x₁ x₂
  have h : (1 - x₁) * (1 - x₂) = 1 - x₁ - x₂ + x₁ * x₂ := by ring
  exact h.ge
