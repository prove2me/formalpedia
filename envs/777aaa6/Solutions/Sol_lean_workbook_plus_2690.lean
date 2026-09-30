-- Prove2me | solution 1 for lean_workbook_plus_2690
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:47.86803+00:00
-- url     : https://prove2.me/submissions/d146755f-dfc5-42e6-96e7-55948b676c36

import Mathlib

theorem solution (a b c : ℝ) :
    a ^ 2 + b ^ 2 + c ^ 2 + 4 * a * b ≥ 2 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a + b - c)]
