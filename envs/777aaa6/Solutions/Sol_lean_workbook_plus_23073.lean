-- Prove2me | solution 1 for lean_workbook_plus_23073
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:59.428083+00:00
-- url     : https://prove2.me/submissions/4ab20b5d-eb1d-4162-9698-5848cf82ee2c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b : ℝ, 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a-b)]
