-- Prove2me | solution 1 for lean_workbook_plus_61330
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:49.283119+00:00
-- url     : https://prove2.me/submissions/b7d7d285-6858-4270-b95a-1cbedb42637f

import Mathlib
set_option autoImplicit false

theorem solution (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - x * z ≥ 3 / 4 * (x - y) ^ 2   := by
  have h1: 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  have h2: 0 ≤ (x + y - 2 * z) ^ 2 := sq_nonneg (x + y - 2 * z)
  linarith [h1, h2]

#print axioms solution
