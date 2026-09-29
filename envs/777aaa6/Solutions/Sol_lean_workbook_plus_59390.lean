-- Prove2me | solution 1 for lean_workbook_plus_59390
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:43:41.253987+00:00
-- url     : https://prove2.me/submissions/05683e09-7142-482b-8f84-3f1dd65ff9df

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0) (h : 2 * a = a * b + b ^ 2) : (a - b) * ((a + b) ^ 3 + 2 * a * b * (a + b) - 2 * a - 10 * b) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
