-- Prove2me | solution 1 for lean_workbook_plus_60125
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:22.190289+00:00
-- url     : https://prove2.me/submissions/aba8d605-e444-4886-a204-7c18e9c2b4a3

import Mathlib

theorem solution (a b c : ℝ) (ha : a ^ 2 = 2 * b + 1)
    (hb : b ^ 2 = 2 * c + 1) : a + b + c ≥ -3 / 2 := by
  nlinarith [sq_nonneg (a + 1), sq_nonneg b]
