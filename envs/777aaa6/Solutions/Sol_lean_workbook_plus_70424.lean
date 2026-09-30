-- Prove2me | solution 1 for lean_workbook_plus_70424
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:28.521101+00:00
-- url     : https://prove2.me/submissions/93ca8875-66ab-4477-be58-7f9c28604a5e

import Mathlib
set_option autoImplicit false

theorem solution {a b c d : ℝ} :
    2 * (a * b + b * c + c * d + d * a + a * c + b * d) ≤
    3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

#print axioms solution
