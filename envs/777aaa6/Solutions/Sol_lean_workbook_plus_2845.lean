-- Prove2me | solution 1 for lean_workbook_plus_2845
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:49.91714+00:00
-- url     : https://prove2.me/submissions/2be7a2c2-0bb1-4c93-ae0b-e5565b6d40a5

import Mathlib

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
