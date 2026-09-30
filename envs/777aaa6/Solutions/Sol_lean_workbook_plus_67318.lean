-- Prove2me | solution 1 for lean_workbook_plus_67318
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:36.736681+00:00
-- url     : https://prove2.me/submissions/40c5a472-6e36-41bc-ac64-bd8068e7f757

import Mathlib
set_option autoImplicit false

theorem solution (x : ℂ) : 4 * x ^ 2 - 4 * x + 1 = 0 ↔ x = 1 / 2   := by
  constructor
  · intro h
    have hs : (2 * x - 1) ^ 2 = 0 := by linear_combination h
    have hz : 2 * x - 1 = 0 := (pow_eq_zero hs)
    linear_combination hz / 2
  · intro h
    rw [h]
    norm_num

#print axioms solution
