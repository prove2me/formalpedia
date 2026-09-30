-- Prove2me | solution 1 for lean_workbook_plus_67230
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:41.616283+00:00
-- url     : https://prove2.me/submissions/bb76dc2f-9354-4e4e-8e6f-dbeca39a2721

import Mathlib
set_option autoImplicit false

theorem solution : ¬ (∀ x y z : ℝ, (x ^ 5 + y ^ 5 + z ^ 5) * (x + y + z) ≥ (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 4 + y ^ 4 + z ^ 4)) := by
  intro h
  have bad := h 1 (-1) 0
  norm_num at bad
  have hb : (1 + 1) * (1 + 1) ≤ (0 : ℝ) := bad
  have hp : (0 : ℝ) < (1 + 1) * (1 + 1) :=
    mul_pos (add_pos zero_lt_one zero_lt_one) (add_pos zero_lt_one zero_lt_one)
  exact (not_le_of_gt hp) hb

#print axioms solution
