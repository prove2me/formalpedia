-- Prove2me | solution 1 for lean_workbook_plus_35496
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:08.28425+00:00
-- url     : https://prove2.me/submissions/f9005a29-30c4-4c3f-bb47-446073ba79ad

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx: x >= 0) : 3 * x ^ 3 - 6 * x ^ 2 + 32 / 9 ≥ 0 := by
  nlinarith [mul_nonneg (sq_nonneg (3*x-4)) (show 0≤3*x+2 by linarith)]
