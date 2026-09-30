-- Prove2me | solution 1 for lean_workbook_plus_69201
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:23.210594+00:00
-- url     : https://prove2.me/submissions/e4b5a85a-20b3-45ea-84ce-9adfbdbf0607

import Mathlib

set_option autoImplicit false

theorem solution (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) ≥ (a₁ * b₁ + a₂ * b₂) ^ 2 := by
  nlinarith [sq_nonneg (a₁ * b₂ - a₂ * b₁)]
