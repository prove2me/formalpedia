-- Prove2me | solution 1 for lean_workbook_plus_44862
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:24.006579+00:00
-- url     : https://prove2.me/submissions/6613a687-3ef5-4bec-a7b5-6b348af643dd

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : a^6 + 3*a^4*b^2 + 8*b^6 >= 2*a^3*b^3 + 2*a^2*b^4 + 8*a*b^5   := by
  nlinarith [sq_nonneg (a^3 - b^3), sq_nonneg (a^2*b - b^3), sq_nonneg (a*b^2 - b^3)]

#print axioms solution
