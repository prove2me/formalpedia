-- Prove2me | solution 2 for lean_workbook_plus_15509
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:14:20.597301+00:00
-- url     : https://prove2.me/submissions/a9e48a0e-1657-44c0-b71b-c432f665e9e2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c >= 3) : a^2 + b^2 + c^2 >= 3 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
