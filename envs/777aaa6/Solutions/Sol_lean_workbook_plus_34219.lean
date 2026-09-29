-- Prove2me | solution 1 for lean_workbook_plus_34219
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:00:25.31579+00:00
-- url     : https://prove2.me/submissions/6e1b9791-e37f-4884-b8fd-d0851fc922a2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : x > 0) : x^3 - 3*x ≥ -2 := by
  nlinarith [mul_nonneg (sq_nonneg (x-1)) (show 0 ≤ x+2 by linarith)]
