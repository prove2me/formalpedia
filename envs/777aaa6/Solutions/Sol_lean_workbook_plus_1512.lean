-- Prove2me | solution 1 for lean_workbook_plus_1512
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:52.200253+00:00
-- url     : https://prove2.me/submissions/622e15ba-6404-4ada-a407-4dbab9fb6afa

import Mathlib

theorem solution (a b c : ℝ) (hab : a + b + c = 3) :
    a * b + b * c + c * a ≤ 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b + c - 3)]
