-- Prove2me | solution 2 for lean_workbook_plus_3454
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:15:22.082963+00:00
-- url     : https://prove2.me/submissions/6957d863-2831-4a78-a18e-ff8ca3fa30f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ x₁ x₂ : ℝ, (1 - x₁) * (1 - x₂) ≥ 1 - x₁ - x₂ + x₁ * x₂ := by
  (intros; linarith)
