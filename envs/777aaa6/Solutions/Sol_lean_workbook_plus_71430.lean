-- Prove2me | solution 1 for lean_workbook_plus_71430
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:55.342841+00:00
-- url     : https://prove2.me/submissions/f419afa6-ea2b-4ecc-949a-ebe0a08224a2

import Mathlib

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^2 + y^2 + x * y + 25 / 12 ≥ 5 / 2 * (x + y) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 5 / 3)]

#print axioms solution
