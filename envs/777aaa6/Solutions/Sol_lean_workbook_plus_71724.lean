-- Prove2me | solution 1 for lean_workbook_plus_71724
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:51.702292+00:00
-- url     : https://prove2.me/submissions/e1e6ab95-c16d-48c0-a24c-4c981e44dcb9

import Mathlib

theorem solution (x y : ℝ) (h : x + y = 2) :
    x * y * (x ^ 2 + y ^ 2) ≤ 2 := by
  have hy : y = 2 - x := by linarith
  rw [hy]
  nlinarith [sq_nonneg (x * (2 - x) - 1)]

#print axioms solution
