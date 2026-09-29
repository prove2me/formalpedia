-- Prove2me | solution 1 for lean_workbook_plus_22457
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:37.72701+00:00
-- url     : https://prove2.me/submissions/32a8f1c4-98fc-458f-a262-c9cf84f0976d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x₁ x₂ y₁ y₂ : ℝ) : (y₂ - y₁) / (x₂ - x₁) = (y₂ - y₁) / (x₂ - x₁) := by
  norm_num
