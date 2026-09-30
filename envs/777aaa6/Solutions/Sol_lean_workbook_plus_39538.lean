-- Prove2me | solution 1 for lean_workbook_plus_39538
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:34:01.744205+00:00
-- url     : https://prove2.me/submissions/2ce8a009-dec6-496c-8c1a-c9cfc1cf8051

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (h : a^2 * (a + b) = 2) : a^3 + a * b * (a + b) + b^3 ≥ 2 := by
  have hab : 0 < a + b := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (sq_nonneg a) (neg_nonneg.mpr hc)]
  nlinarith [mul_nonneg hab.le (sq_nonneg b)]
