-- Prove2me | solution 1 for lean_workbook_plus_68570
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:52.666464+00:00
-- url     : https://prove2.me/submissions/466ea7eb-968b-4d71-a950-c8d5b79baa34

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (c - a + b) * (c + a - b) ≤ c^2 := by
  intro a b c
  nlinarith [sq_nonneg (a-b)]
