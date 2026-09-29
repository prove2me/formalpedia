-- Prove2me | solution 1 for lean_workbook_plus_53267
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:48.363098+00:00
-- url     : https://prove2.me/submissions/1672d278-88f9-45d7-bd9e-33971b5a7d3f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c: ℝ): 2 * (a ^ 2 + b ^ 2 + c ^ 2) + 6 ≥ 4 * (a + b + c) := by
  nlinarith [sq_nonneg (a-1), sq_nonneg (b-1), sq_nonneg (c-1)]
