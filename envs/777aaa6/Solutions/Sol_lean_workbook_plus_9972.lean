-- Prove2me | solution 1 for lean_workbook_plus_9972
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:36.683055+00:00
-- url     : https://prove2.me/submissions/07a344d8-34f3-4cd4-ba55-33d2d61449f5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) : 18 * x * y ≤ 7 + 8 * x ^ 2 * y ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
