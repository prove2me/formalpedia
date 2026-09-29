-- Prove2me | solution 1 for lean_workbook_plus_20807
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:37:01.048741+00:00
-- url     : https://prove2.me/submissions/580e9771-95f4-4d07-9f5c-a84c05cd7fee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) (h : (b - 1) * (c - 1) ≤ 0) :
  (b + c - 2 * b * c + 1) ^ 2 + (b * c - 1) ^ 2 - 2 * (b - 1) * (c - 1) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
