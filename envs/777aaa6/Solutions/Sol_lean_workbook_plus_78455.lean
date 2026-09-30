-- Prove2me | solution 1 for lean_workbook_plus_78455
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:02:08.212945+00:00
-- url     : https://prove2.me/submissions/4a567e28-f04e-4c6c-a2e2-1fac3b618813

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, 8 * (x * y * z) ^ 2 ≤ (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2)   := by
  intro x y z
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^2 - z^2), sq_nonneg (y^2 - z^2)]

#print axioms solution
