-- Prove2me | solution 1 for lean_workbook_plus_42805
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:57.821148+00:00
-- url     : https://prove2.me/submissions/feb6b373-71f6-4340-af42-079349e26e77

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : (1 + x + y) ^ 2 ≥ 3 * (x + y + x * y) := by
  nlinarith [sq_nonneg (x-y),sq_nonneg (x-1),sq_nonneg (y-1)]
