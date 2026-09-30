-- Prove2me | solution 1 for lean_workbook_plus_37004
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:16.418774+00:00
-- url     : https://prove2.me/submissions/408204cf-ec07-46c5-a87d-768c3730dcfa

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 8 * (x^4 + y^4 + x*y^3 + y*x^3) ≤ 9 * (x^4 + y^4 + 2*x^2*y^2)   := by
  nlinarith [sq_nonneg (x ^ 2 - 4 * x * y + y ^ 2)]

#print axioms solution
