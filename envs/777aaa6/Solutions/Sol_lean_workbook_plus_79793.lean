-- Prove2me | solution 1 for lean_workbook_plus_79793
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:01.868388+00:00
-- url     : https://prove2.me/submissions/7a1fc23c-a70f-4e96-a0d7-53ad536cdc4c

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : x ≤ 1) : x^4-x^3+x^2-x+1 > 0 := by
  nlinarith [sq_nonneg (x^2-x/2), sq_nonneg (x-2/3)]

#print axioms solution
