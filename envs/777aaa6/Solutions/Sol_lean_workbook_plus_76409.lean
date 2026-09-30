-- Prove2me | solution 1 for lean_workbook_plus_76409
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:09:38.549728+00:00
-- url     : https://prove2.me/submissions/7e93a7ab-d576-4176-a771-e56cce520614

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : a^2 / 4 + b^2 + c^2 - a * b + a * c - 2 * b * c ≥ 0   := by
  nlinarith [sq_nonneg (a / 2 - b + c)]

#print axioms solution
