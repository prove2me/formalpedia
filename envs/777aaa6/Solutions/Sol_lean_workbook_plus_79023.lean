-- Prove2me | solution 1 for lean_workbook_plus_79023
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:35.057634+00:00
-- url     : https://prove2.me/submissions/7541b0d5-b6f6-47ef-951f-4040ae53188e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 ≥ (1/3)*(a + b + c)^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
