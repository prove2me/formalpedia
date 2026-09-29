-- Prove2me | solution 1 for lean_workbook_plus_16357
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:50.196298+00:00
-- url     : https://prove2.me/submissions/2a0a00c6-6e67-4d64-a57d-6d81709e036f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x^3 + y^3 + 2 ≥ 2 * x * y + x + y := by
  nlinarith [mul_nonneg (sq_nonneg (x-1)) (show 0 ≤ x+1 by linarith), mul_nonneg (sq_nonneg (y-1)) (show 0 ≤ y+1 by linarith), sq_nonneg (x-y)]
