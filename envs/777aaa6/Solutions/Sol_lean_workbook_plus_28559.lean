-- Prove2me | solution 1 for lean_workbook_plus_28559
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:18.192109+00:00
-- url     : https://prove2.me/submissions/3596f875-8073-4cb0-973d-d5e52b4e7e18

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (h : x + y = 0) : (x + Real.sqrt (1 + x^2)) * (y + Real.sqrt (1 + y^2)) = 1 := by
  have hy : y = -x := by linarith
  rw [hy]
  simp only [neg_sq]
  have hs := Real.sq_sqrt (show 0 ≤ 1+x^2 by positivity)
  nlinarith
