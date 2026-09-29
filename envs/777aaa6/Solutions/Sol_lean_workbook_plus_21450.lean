-- Prove2me | solution 1 for lean_workbook_plus_21450
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:12:59.613848+00:00
-- url     : https://prove2.me/submissions/e6218b53-05e4-441a-ba66-38e2ce112bfe

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (x y z : ℝ) (h : x * y + x * z + y * z ≥ 3) : (x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z + 3) / (x + y + z) ^ 2 ≤ 1 := by
  have hp : 0 < (x+y+z)^2 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  apply (div_le_one hp).2
  nlinarith
