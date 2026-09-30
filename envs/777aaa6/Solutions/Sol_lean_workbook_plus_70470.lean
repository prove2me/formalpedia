-- Prove2me | solution 1 for lean_workbook_plus_70470
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:16.105074+00:00
-- url     : https://prove2.me/submissions/73fe90ff-b7e3-47ca-930b-d6849faf3142

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 3 ≤ x) : x^7 - 3^7 * x + 2 * 3^7 ≥ 0 := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : 9 ≤ x^2 := by nlinarith
  have hq : 0 ≤ x^6 + 3*x^5 + 9*x^4 + 27*x^3 + 81*x^2 + 243*x - 1458 := by
    nlinarith [pow_nonneg hx0 6, pow_nonneg hx0 5, pow_nonneg hx0 4, pow_nonneg hx0 3]
  have hp := mul_nonneg (sub_nonneg.mpr hx) hq
  nlinarith

#print axioms solution
