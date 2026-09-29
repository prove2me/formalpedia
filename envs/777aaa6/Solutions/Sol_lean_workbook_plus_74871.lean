-- Prove2me | solution 1 for lean_workbook_plus_74871
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:28.167089+00:00
-- url     : https://prove2.me/submissions/5f0fe0be-b865-4464-bd27-5db986d06e4c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (c d : ℝ) : (c^2 + (2 * d - 2) * c + d^2 - 2 * d + 1) ≥ 0 := by
  nlinarith [sq_nonneg (c+d-1)]
