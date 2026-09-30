-- Prove2me | solution 1 for lean_workbook_plus_66608
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:04.952792+00:00
-- url     : https://prove2.me/submissions/b98938c8-32c1-4bfc-bf30-e4485d2036a1

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : 2 * (1 - a + a^2) * (1 - b + b^2) ≥ 1 + a^2 * b^2   := by
  nlinarith [sq_nonneg (a - b), sq_nonneg ((1 - a) * (1 - b))]

#print axioms solution
