-- Prove2me | solution 1 for lean_workbook_plus_14681
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:50.709256+00:00
-- url     : https://prove2.me/submissions/ca8906a2-0435-48d4-963d-f7f795ac8b83

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) : a^2 + 2*a + 1 ≥ 8*a - 8*a^2   := by
  nlinarith [sq_nonneg (3 * a - 1)]

#print axioms solution
