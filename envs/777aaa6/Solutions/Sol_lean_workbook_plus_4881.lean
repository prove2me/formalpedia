-- Prove2me | solution 1 for lean_workbook_plus_4881
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:24.636988+00:00
-- url     : https://prove2.me/submissions/a7ca825c-78e8-4836-bbe7-6070a5c21706

import Mathlib

theorem solution (a b c : ℝ) :
    ((a + b) ^ 2 - c ^ 2) * (c ^ 2 - (a - b) ^ 2) ≤ 4 * a ^ 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2)]
