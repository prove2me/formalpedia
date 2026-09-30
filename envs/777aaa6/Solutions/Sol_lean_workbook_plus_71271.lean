-- Prove2me | solution 1 for lean_workbook_plus_71271
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:19.834918+00:00
-- url     : https://prove2.me/submissions/93a962a5-a4ea-46ed-91b7-fd6fbbc92a88

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) :
    a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) ≥ 0 := by
  nlinarith [sq_nonneg (a + b + c)]

#print axioms solution
