-- Prove2me | solution 1 for lean_workbook_plus_21840
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:22.076424+00:00
-- url     : https://prove2.me/submissions/935ed2ec-3824-404d-8525-1b9bd251896c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a + b = 9) (h₂ : a * (a - 2) + b * (b - 2) = 21) : a * b = 21 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
