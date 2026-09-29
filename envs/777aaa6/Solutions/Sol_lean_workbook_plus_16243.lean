-- Prove2me | solution 1 for lean_workbook_plus_16243
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:47.937859+00:00
-- url     : https://prove2.me/submissions/3d0d407d-0bd9-48a6-b521-7a4d28993562

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x + y + z ≥ Real.sqrt (3 * (x * y + x * z + y * z)) := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · nlinarith [sq_nonneg (x-y), sq_nonneg (x-z), sq_nonneg (y-z)]
