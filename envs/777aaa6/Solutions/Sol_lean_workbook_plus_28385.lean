-- Prove2me | solution 1 for lean_workbook_plus_28385
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:42.882741+00:00
-- url     : https://prove2.me/submissions/3fc9e2f3-8946-4656-906f-8a7cd454429f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b + c = 11) (h₂ : a^2 + b^2 + c^2 = 49) : a * b + b * c + c * a = 36 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
