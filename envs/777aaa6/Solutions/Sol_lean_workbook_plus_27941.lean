-- Prove2me | solution 1 for lean_workbook_plus_27941
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:44:08.952097+00:00
-- url     : https://prove2.me/submissions/7503aa8b-a112-4bb1-bb9e-edf1ab451a6b

import Mathlib

set_option autoImplicit false

theorem solution (x y z : Real) :
    x ^ 4 + y ^ 4 + z ^ 4 ≥ (x + y + z) ^ 4 / 27 := by
  have h1 : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h2 : (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 ≤ 3 * (x ^ 4 + y ^ 4 + z ^ 4) := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2),
      sq_nonneg (z ^ 2 - x ^ 2)]
  have hm : 0 ≤ (3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2) *
      (3 * (x ^ 2 + y ^ 2 + z ^ 2) + (x + y + z) ^ 2) :=
    mul_nonneg (sub_nonneg.mpr h1) (by positivity)
  nlinarith only [h2, hm]

#print axioms solution
