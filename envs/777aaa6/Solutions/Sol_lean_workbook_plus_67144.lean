-- Prove2me | solution 1 for lean_workbook_plus_67144
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:21.8653+00:00
-- url     : https://prove2.me/submissions/641b6d75-108b-47f8-955b-4f865c9bd8a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (b : ℝ) (h₁ : x + 2 = 0) (h₂ : b = 0) : x = -2 ∧ b = 0 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (b), sq_nonneg (x - b), sq_nonneg (x + b)])
