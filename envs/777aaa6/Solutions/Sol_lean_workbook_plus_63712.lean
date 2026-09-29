-- Prove2me | solution 1 for lean_workbook_plus_63712
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:33.799565+00:00
-- url     : https://prove2.me/submissions/d2ab1316-ff10-4d18-8716-c1d2f1b72d4c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) : x ^ 2 + 2 * x * y + y ^ 2 + 1 ≥ 2 * x * y + 2 * y := by
  nlinarith [sq_nonneg x, sq_nonneg (y-1)]
