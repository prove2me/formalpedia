-- Prove2me | solution 1 for lean_workbook_plus_26400
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:09.997944+00:00
-- url     : https://prove2.me/submissions/e7bacb46-9556-4551-bec4-5521c6290774

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) : 4 * z ^ 2 + x ^ 2 + y ^ 2 + 2 * x * y ≥ 3 * z * (x + y) := by
  nlinarith [sq_nonneg (2*x+2*y-3*z), sq_nonneg z]
