-- Prove2me | solution 1 for lean_workbook_plus_44760
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:14:12.59894+00:00
-- url     : https://prove2.me/submissions/aa46e3c9-a8ab-4ccb-9819-d27373390506

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + 1) * (c ^ 2 + 2) ≥ 3 * (a + b + c) ^ 2   := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a * c - 1),
    sq_nonneg (b * c - 1)]

#print axioms solution
