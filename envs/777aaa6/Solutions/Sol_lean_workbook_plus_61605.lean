-- Prove2me | solution 1 for lean_workbook_plus_61605
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:44.394156+00:00
-- url     : https://prove2.me/submissions/351f3edb-f0bd-422e-a857-35c4f9b36915

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : (16*x^4 - 32*x^3 + 28*x^2 - 12*x + 9) * (2*x - 1)^2 ≥ 0   := by
  have he : 16 * x ^ 4 - 32 * x ^ 3 + 28 * x ^ 2 - 12 * x + 9 =
      (2 * x - 1) ^ 4 + (2 * x - 1) ^ 2 + 7 := by ring
  rw [he]
  positivity

#print axioms solution
