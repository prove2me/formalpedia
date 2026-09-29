-- Prove2me | solution 1 for lean_workbook_plus_20524
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:45.754641+00:00
-- url     : https://prove2.me/submissions/6f9dc813-ef48-4672-bc29-38fdb2d0800a

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : x*y + y*z + z*x ≤ 1/3 := by
  nlinarith [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
