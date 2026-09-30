-- Prove2me | solution 1 for lean_workbook_plus_74106
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:22:26.831547+00:00
-- url     : https://prove2.me/submissions/89ec557c-df96-4832-be7b-8ad58140a3d7

import Mathlib

theorem solution (a b : ℝ) :
    Real.sqrt ((a^2 + b^2) * (4 * b^2 + a^2)) ≥ 3 * a * b := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (a ^ 2 - 2 * b ^ 2)]

#print axioms solution
