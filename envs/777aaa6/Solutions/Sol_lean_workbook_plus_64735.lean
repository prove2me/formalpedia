-- Prove2me | solution 1 for lean_workbook_plus_64735
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:25.912841+00:00
-- url     : https://prove2.me/submissions/4c898f88-e270-4ae0-b00a-c568e9d26fb1

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : 2 * (x^6 + 1) ≥ (x^3 + 1)^2   := by
  nlinarith [sq_nonneg (x^3 - 1)]

#print axioms solution
