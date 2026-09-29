-- Prove2me | solution 1 for lean_workbook_plus_36349
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:42:01.957938+00:00
-- url     : https://prove2.me/submissions/987cfc74-b9a2-4dbd-a942-6c595c870646

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : (a * b + c * d) * (b * c + d * a) ≤ (a * b + b * c + c * d + d * a) ^ 2 / 4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (a + d), sq_nonneg (b + c), sq_nonneg (b + d), sq_nonneg (c + d)])
