-- Prove2me | solution 1 for lean_workbook_plus_1500
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:34.033426+00:00
-- url     : https://prove2.me/submissions/098a451e-b011-46cf-9168-6719071c84c6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : (1 + 1 / 4) * (x ^ 2 + 4 * y ^ 2) ≥ (x + y) ^ 2 := by
  nlinarith [sq_nonneg (x-4*y)]
