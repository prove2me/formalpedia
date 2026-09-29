-- Prove2me | solution 1 for lean_workbook_plus_42343
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:23.799945+00:00
-- url     : https://prove2.me/submissions/806020a3-1684-4c22-9542-c5579133f8dd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a * b = 1) : a ^ 2 + b ^ 2 + 4 ≥ 3 * (a + b) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
