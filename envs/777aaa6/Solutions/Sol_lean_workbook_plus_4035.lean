-- Prove2me | solution 1 for lean_workbook_plus_4035
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:01.641694+00:00
-- url     : https://prove2.me/submissions/f33d3534-17dd-4694-81ca-910a23e0b117

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution {x y z : ℝ} (h : x + y + z = 0) :
  4 * (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2) ≥ (2 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2 := by
  have hz : z = -x-y := by linarith
  rw [hz]
  nlinarith [sq_nonneg (x*y*(-x-y))]
