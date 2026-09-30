-- Prove2me | solution 1 for lean_workbook_plus_70840
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:15.212336+00:00
-- url     : https://prove2.me/submissions/0e28dfa5-845c-4152-aa40-f8f445b54eaf

import Mathlib
set_option autoImplicit false

theorem solution {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x^4 + x^3*y + x^2*y^2 + x*y^3 + y^4 > 0 := by
  have hp := sq_pos_of_ne_zero (mul_ne_zero hx hy)
  nlinarith [sq_nonneg (x^2 + x*y/2), sq_nonneg (y^2 + x*y/2)]

#print axioms solution
