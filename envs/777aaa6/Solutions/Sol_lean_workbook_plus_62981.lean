-- Prove2me | solution 1 for lean_workbook_plus_62981
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:33.777084+00:00
-- url     : https://prove2.me/submissions/2c102a61-66c0-4e0c-a0b1-d029ca261ef1

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : x ^ 2 + x * y + y ^ 2 > 0   := by
  have hp : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  nlinarith [hp, sq_nonneg y, sq_nonneg (x + y)]

#print axioms solution
