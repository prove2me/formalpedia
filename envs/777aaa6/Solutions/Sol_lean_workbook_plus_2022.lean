-- Prove2me | solution 1 for lean_workbook_plus_2022
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:07.467876+00:00
-- url     : https://prove2.me/submissions/f508cde2-04c4-4cc5-973b-f670b824431a

import Mathlib
set_option autoImplicit false

theorem solution (a b c u v w : ℝ) (h : a + b + c ≥ a * b * c) : (u + v + w) ^ 2 ≥ 3 * (u * v + v * w + w * u)   := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u)]

#print axioms solution
