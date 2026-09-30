-- Prove2me | solution 1 for lean_workbook_plus_56634
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:41.690163+00:00
-- url     : https://prove2.me/submissions/ca19aba3-cd4c-4c5c-a52d-578eaf13105b

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, 1 / 2 * x ^ 2 * y ^ 2 * z ^ 2 + 1 / 2 * y ^ 6 ≥ x * y ^ 4 * z   := by
  intro x y z
  nlinarith [sq_nonneg (x * y * z - y^3)]

#print axioms solution
