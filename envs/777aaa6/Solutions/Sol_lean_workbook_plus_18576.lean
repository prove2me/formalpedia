-- Prove2me | solution 1 for lean_workbook_plus_18576
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:44.643563+00:00
-- url     : https://prove2.me/submissions/93e37835-a481-403f-a50f-779da755fc49

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a + b = 6) : 18 ≤ a^2 + b^2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
