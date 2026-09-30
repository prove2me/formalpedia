-- Prove2me | solution 1 for lean_workbook_plus_17600
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:58.837175+00:00
-- url     : https://prove2.me/submissions/3e235f9d-339b-456c-971d-bc46ad720f28

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 1 ≤ x) : x^4 - x^3 + x^2 - x + 1 > 0   := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hx
  nlinarith only [mul_nonneg (pow_nonneg hx0 3) hx1, mul_nonneg hx0 hx1]

#print axioms solution
