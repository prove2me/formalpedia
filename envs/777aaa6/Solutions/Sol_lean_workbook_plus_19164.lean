-- Prove2me | solution 1 for lean_workbook_plus_19164
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:12.262453+00:00
-- url     : https://prove2.me/submissions/720527bd-81e9-4604-b63a-4033150067c7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x y : ℝ, 4 * (x ^ 2 + x * y + y ^ 2) ≥ 3 * (x + y) ^ 2 := by
  intro x y
  nlinarith [sq_nonneg (x-y)]
