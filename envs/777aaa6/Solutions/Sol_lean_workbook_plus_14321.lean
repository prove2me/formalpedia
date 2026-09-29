-- Prove2me | solution 1 for lean_workbook_plus_14321
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:32.430086+00:00
-- url     : https://prove2.me/submissions/7b0de76e-f819-4390-98f0-94cb2b2e61b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h : a + b = 4) : a * b ≤ 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
