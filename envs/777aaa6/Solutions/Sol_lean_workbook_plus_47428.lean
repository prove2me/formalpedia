-- Prove2me | solution 1 for lean_workbook_plus_47428
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:31.837123+00:00
-- url     : https://prove2.me/submissions/c4366c79-c436-45a6-a4b7-b458542f9738

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) : 3*x^4 + 1 ≥ 4*x^3   := by
  nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x^2 - x)]

#print axioms solution
