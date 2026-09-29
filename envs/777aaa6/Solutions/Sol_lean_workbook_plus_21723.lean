-- Prove2me | solution 1 for lean_workbook_plus_21723
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:39.679179+00:00
-- url     : https://prove2.me/submissions/17f16794-3224-4cd1-9c6a-3f1b66e631c0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h : a + b + c + d = 0) : a^3 + b^3 + c^3 + d^3 = 3 * (a + d) * (b + d) * (c + d) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
