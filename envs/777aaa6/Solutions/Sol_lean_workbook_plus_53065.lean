-- Prove2me | solution 1 for lean_workbook_plus_53065
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:12.057395+00:00
-- url     : https://prove2.me/submissions/d5b4e15c-6c12-4c8f-9b6f-23d875b5814e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a > 0 ∧ b > 0 ∧ c > 0) (habc : a * b + b * c + c * a = 3) : a * b * c * (a + b + c) ≤ 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
