-- Prove2me | solution 1 for lean_workbook_plus_28925
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:37.197655+00:00
-- url     : https://prove2.me/submissions/7bc1299a-f938-4a7d-b6ee-0d8e0f61d797

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (t : ℝ) : t^4 - 4 * t^3 + 6 * t^2 - 4 * t + 1 ≥ 0 := by
  nlinarith [sq_nonneg ((t-1)^2)]
