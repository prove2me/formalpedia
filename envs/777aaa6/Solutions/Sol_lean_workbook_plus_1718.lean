-- Prove2me | solution 1 for lean_workbook_plus_1718
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:48.53573+00:00
-- url     : https://prove2.me/submissions/527a57f0-f3c3-40a3-9286-47e69a7882f3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r m o : ℝ) : (r + m + o) ^ 2 ≥ 3 * (r * m + m * o + o * r) := by
  (intros; nlinarith [sq_nonneg (r), sq_nonneg (m), sq_nonneg (o), sq_nonneg (r - m), sq_nonneg (r - o), sq_nonneg (m - o), sq_nonneg (r + m), sq_nonneg (r + o), sq_nonneg (m + o)])
