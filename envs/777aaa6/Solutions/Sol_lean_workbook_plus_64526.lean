-- Prove2me | solution 1 for lean_workbook_plus_64526
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:18:15.13506+00:00
-- url     : https://prove2.me/submissions/e57380ec-b477-49c5-bc22-6e45219a60aa

import Mathlib
set_option autoImplicit false

theorem solution (k : ℝ) (h : k >= 1/2) : k^3 - 2 * k^2 + k + 1 > 0   := by
  nlinarith [pow_two_nonneg (k - 1)]

#print axioms solution
