-- Prove2me | solution 1 for lean_workbook_plus_32251
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:21.500991+00:00
-- url     : https://prove2.me/submissions/db0faf49-abaf-458f-be41-0104699eca42

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + 1/y = 1/5) (hxy : y + 1/x = 20) : x*y = 1 := by
  field_simp at *
  nlinarith [sq_nonneg (10*x-1)]
