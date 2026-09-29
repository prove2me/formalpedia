-- Prove2me | solution 1 for lean_workbook_plus_27487
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:39.610272+00:00
-- url     : https://prove2.me/submissions/9ab7034d-c705-47c3-b96a-58c67ff05b95

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z t : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (ht : t > 0) : x * y + y * z + z * t + t * x ≤ 1 / 4 * (x + y + z + t) ^ 2 := by
  nlinarith [sq_nonneg (x+z-y-t)]
