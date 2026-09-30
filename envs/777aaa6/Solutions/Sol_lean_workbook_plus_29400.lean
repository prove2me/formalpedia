-- Prove2me | solution 1 for lean_workbook_plus_29400
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:05.617055+00:00
-- url     : https://prove2.me/submissions/efa59987-9404-4b27-ac5e-86322610abff

import Mathlib
set_option autoImplicit false

theorem solution :  ∀ x y z : ℝ, x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) ≥ 2 * (x ^ 3 * (y + z) + y ^ 3 * (x + z) + z ^ 3 * (x + y))   := by
  intro x y z
  nlinarith only [sq_nonneg ((x - y) ^ 2), sq_nonneg ((x - z) ^ 2), sq_nonneg ((y - z) ^ 2)]

#print axioms solution
