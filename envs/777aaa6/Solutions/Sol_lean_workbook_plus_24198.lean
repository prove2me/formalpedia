-- Prove2me | solution 1 for lean_workbook_plus_24198
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:41.566019+00:00
-- url     : https://prove2.me/submissions/45a8a19a-6388-4ec5-b4dc-757fc1ab6d1d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h : a + b + c + d = 0) : a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = 3 * (a * b * c + b * c * d + c * d * a + d * a * b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
