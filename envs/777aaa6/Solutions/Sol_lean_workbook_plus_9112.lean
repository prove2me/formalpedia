-- Prove2me | solution 1 for lean_workbook_plus_9112
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:48.722351+00:00
-- url     : https://prove2.me/submissions/e55b3f6f-9caa-4686-9344-e6ccc1101df8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (ha : 0 < a) : a^5 + 1 ≥ a^3 + a^2 := by
  have hp : 0 ≤ a^3+2*a^2+2*a+1 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (a-1)) hp]
