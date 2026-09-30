-- Prove2me | solution 1 for lean_workbook_plus_10224
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:23.649159+00:00
-- url     : https://prove2.me/submissions/cefe53fe-12a7-4976-8bca-bd9dbd8f3bcd

import Mathlib

theorem solution (x y : ℝ) :
    1 + x^2 + y^2 + 2 * x * y ≤ (4:ℝ) / 3 * (1 + x^2) * (1 + y^2) := by
  nlinarith only [sq_nonneg (x - y), sq_nonneg (2 * x * y - 1)]

#print axioms solution
