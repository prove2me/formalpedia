-- Prove2me | solution 1 for lean_workbook_plus_61599
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:45.183352+00:00
-- url     : https://prove2.me/submissions/391c26f8-5d14-447a-a6a2-9df464af614d

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) : (x - z) ^ 2 ≤ 2 * ((x - y) ^ 2 + (y - z) ^ 2)   := by
  rw [add_comm]
  nlinarith [sq_nonneg (x - y - (y - z))]

#print axioms solution
