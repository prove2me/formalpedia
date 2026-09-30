-- Prove2me | solution 1 for lean_workbook_plus_6289
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:26.728222+00:00
-- url     : https://prove2.me/submissions/4ccba303-001f-4449-bc27-cdf8fa3aa59c

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) :
  26 * x ^ 2 + 39 * y ^ 2 + 52 * z ^ 2 ≥ 12 * (x + y + z) ^ 2   := by
  nlinarith [sq_nonneg (2 * x - 3 * y), sq_nonneg (x - 2 * z),
    sq_nonneg (3 * y - 4 * z)]

#print axioms solution
