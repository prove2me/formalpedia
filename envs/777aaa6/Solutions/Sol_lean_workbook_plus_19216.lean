-- Prove2me | solution 1 for lean_workbook_plus_19216
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:45.248422+00:00
-- url     : https://prove2.me/submissions/182ad6f0-bd8d-475c-aa71-b3872510caf1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x) : 3 + x ^ 4 ≥ 4 * x := by
  have hp : 0 ≤ x^2+2*x+3 := by nlinarith [sq_nonneg (x+1)]
  nlinarith [mul_nonneg (sq_nonneg (x-1)) hp]
