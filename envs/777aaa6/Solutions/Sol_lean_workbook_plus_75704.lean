-- Prove2me | solution 1 for lean_workbook_plus_75704
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:09:28.600207+00:00
-- url     : https://prove2.me/submissions/ed8f22af-e53d-49dc-a01d-9e537e8af551

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) :
    (a+b)*(a^2+b^2)*(a^3+b^3) ≤ 4 * (a^6 + b^6) := by
  have hquad : 0 ≤ 3*a^2 + 5*a*b + 3*b^2 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have hnonneg := mul_nonneg
    (mul_nonneg (sq_nonneg (a - b)) (add_nonneg (sq_nonneg a) (sq_nonneg b))) hquad
  nlinarith [hnonneg]
