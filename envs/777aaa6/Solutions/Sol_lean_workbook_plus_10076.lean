-- Prove2me | solution 1 for lean_workbook_plus_10076
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:09:02.765059+00:00
-- url     : https://prove2.me/submissions/600d64bb-4bb1-4c5d-ad95-a75fff5a0789

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : 0 < x) : x ^ 6 + 2 - (x ^ 3 + x ^ 2 + x) ≥ 0 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 3 - x),
    sq_nonneg (x ^ 2 - x), mul_pos hx hx, mul_nonneg hx.le (sq_nonneg (x - 1)),
    mul_nonneg (mul_pos hx hx).le (sq_nonneg (x - 1)),
    mul_nonneg (pow_pos hx 3).le (sq_nonneg (x - 1)),
    mul_nonneg (pow_pos hx 4).le (sq_nonneg (x - 1))]
