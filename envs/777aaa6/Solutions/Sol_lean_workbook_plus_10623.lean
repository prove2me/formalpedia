-- Prove2me | solution 1 for lean_workbook_plus_10623
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:05:07.590911+00:00
-- url     : https://prove2.me/submissions/e775a429-83c7-4bfc-be6f-78240d3b266a

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x > 1/4, Real.sqrt x < 2 * x := by
  intro x hx
  have hp : 0 < 2*x := by linarith
  apply (Real.sqrt_lt' hp).2
  nlinarith [mul_pos (show 0<x by linarith) (show 0<4*x-1 by linarith)]
