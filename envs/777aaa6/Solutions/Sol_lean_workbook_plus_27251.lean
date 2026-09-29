-- Prove2me | solution 1 for lean_workbook_plus_27251
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:46.227727+00:00
-- url     : https://prove2.me/submissions/01e10d1c-101c-4a30-a8f4-2b56cf5e3fc9

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : (x^3 - 1) / 3 ≤ (x^4 - 1) / 4 := by
  have hp : 0 ≤ 3*x^2+2*x+1 := by nlinarith [sq_nonneg (3*x+1)]
  nlinarith [mul_nonneg (sq_nonneg (x-1)) hp]
