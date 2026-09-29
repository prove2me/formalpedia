-- Prove2me | solution 1 for lean_workbook_plus_35908
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:22.855744+00:00
-- url     : https://prove2.me/submissions/9a8c6dc8-543a-44d5-b823-75e58dcb9fb5

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (h : x > 0) : (x + 1) ^ 2 ≥ 4 * x := by
  nlinarith [sq_nonneg (x-1)]
