-- Prove2me | solution 1 for lean_workbook_plus_70510
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:27.715746+00:00
-- url     : https://prove2.me/submissions/0ffb9017-3ea9-4a25-a939-b343ba192b96

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℚ) (hx : x = 9/2) (hy : y = 1/2) :
    1/x + 1/y = 20/9 := by
  subst x
  subst y
  norm_num

#print axioms solution
