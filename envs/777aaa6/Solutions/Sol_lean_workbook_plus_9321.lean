-- Prove2me | solution 1 for lean_workbook_plus_9321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:05.362315+00:00
-- url     : https://prove2.me/submissions/a2bd6b34-ffc2-421c-90a3-70ce6fcd520a

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) : x * (y - x) ≤ (x + (y - x))^2 / 4 := by
  nlinarith [sq_nonneg (2*x-y)]
