-- Prove2me | solution 1 for lean_workbook_plus_15300
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:30.955939+00:00
-- url     : https://prove2.me/submissions/050ff5a9-4a17-4315-a2b5-38cb6a5a8380

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x) : Real.sqrt x ≤ (1 + x) / 2 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · nlinarith [sq_nonneg (x-1)]
