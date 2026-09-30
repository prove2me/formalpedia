-- Prove2me | solution 1 for lean_workbook_plus_71202
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:21.090795+00:00
-- url     : https://prove2.me/submissions/d0ae9859-6b35-4e77-a06d-67a4295ef413

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) :
    2 * (x ^ 2 + y ^ 2) ^ 3 ≥ (x ^ 3 + y ^ 3) * (x + y) ^ 3 := by
  have hq : 0 ≤ x ^ 2 + x * y + y ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]
  have h := mul_nonneg (show 0 ≤ (x - y) ^ 4 by positivity) hq
  nlinarith [show 2 * (x ^ 2 + y ^ 2) ^ 3 - (x ^ 3 + y ^ 3) * (x + y) ^ 3 =
    (x - y) ^ 4 * (x ^ 2 + x * y + y ^ 2) by ring]

#print axioms solution
