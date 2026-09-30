-- Prove2me | solution 1 for lean_workbook_plus_52789
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:38.247559+00:00
-- url     : https://prove2.me/submissions/4d9e2890-c272-4e3c-87bc-de6b5ce2d635

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (h : a^2 * b^2 + a + b = 7 * a * b) :
  a * b + a + b ≤ 16   := by
  nlinarith only [h, sq_nonneg (a * b - 4)]

#print axioms solution
