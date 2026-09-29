-- Prove2me | solution 1 for lean_workbook_plus_54901
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:02:01.809339+00:00
-- url     : https://prove2.me/submissions/4e0f5661-415c-492b-8417-d68d83bebc52

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : 8 * (a ^ 3 * b + b ^ 3 * a) ≤ a ^ 4 + b ^ 4 + 4 * (b ^ 3 * a + a ^ 3 * b) + 6 * a ^ 2 * b ^ 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
