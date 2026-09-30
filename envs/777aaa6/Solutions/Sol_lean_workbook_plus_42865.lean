-- Prove2me | solution 1 for lean_workbook_plus_42865
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:04:31.39285+00:00
-- url     : https://prove2.me/submissions/3b847e31-61c7-47ae-bd2f-0e65a7263dfa

import Mathlib

set_option autoImplicit false

theorem solution (a b : ℕ) (x : ℝ) (_hx : 0 < x ∧ x < 1) :
    x ^ a / (1 - x) ^ (a + 1) * (x ^ b / (1 - x) ^ (b + 1)) =
      x ^ (a + b) / (1 - x) ^ (a + b + 2) := by
  rw [div_mul_div_comm, ← pow_add, ← pow_add]
  congr 2
  omega

#print axioms solution
