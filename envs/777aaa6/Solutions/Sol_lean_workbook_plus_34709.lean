-- Prove2me | solution 1 for lean_workbook_plus_34709
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:08.084778+00:00
-- url     : https://prove2.me/submissions/c0e6e2c4-9543-4011-a828-132896ec21a2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a x : ℝ) : (x + a ^ 3 - a) * ((x + (1 / 2) * (2 * a ^ 3 + a)) ^ 2 + (3 / 4) * a ^ 2 + 1) = 0 ↔ x = a - a ^ 3 := by
  have hp : 0 < (x+(1/2)*(2*a^3+a))^2+(3/4)*a^2+1 := by positivity
  constructor
  · intro h
    have hz := (mul_eq_zero.mp h).resolve_right (ne_of_gt hp)
    linarith
  · intro h
    rw [h]
    ring
