-- Prove2me | solution 1 for lean_workbook_plus_78498
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:51:12.011297+00:00
-- url     : https://prove2.me/submissions/9073f8bc-8d43-4688-a723-56daffb520e8

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) : (3 * x + y) ^ 2 ≥ 8 * (x ^ 2 - y ^ 2)   := by
  nlinarith only [sq_nonneg (x + 3 * y)]

#print axioms solution
