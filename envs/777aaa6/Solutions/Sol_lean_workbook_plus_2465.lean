-- Prove2me | solution 1 for lean_workbook_plus_2465
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:05.614239+00:00
-- url     : https://prove2.me/submissions/532a61f4-54df-4993-bda6-786996af416f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) : (x + z) ^ 2 - 4 * y * (x + z) + 4 * y ^ 2 ≥ 0 := by
  nlinarith [sq_nonneg (x+z-2*y)]
