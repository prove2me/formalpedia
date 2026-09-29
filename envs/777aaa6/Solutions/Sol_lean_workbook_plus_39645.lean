-- Prove2me | solution 1 for lean_workbook_plus_39645
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:23.806646+00:00
-- url     : https://prove2.me/submissions/3945ce55-287e-4dcf-a4bc-b4dbca6252fe

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ x : ℝ, 5 * x ^ 2 - 4 * x + 11 ≥ 0 := by
  intro x
  nlinarith [sq_nonneg (5*x-2)]
