-- Prove2me | solution 1 for lean_workbook_plus_15374
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:11:02.172092+00:00
-- url     : https://prove2.me/submissions/84effdb5-2c6d-44e0-93c0-cda0f0ce18fb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution : ∀ x : ℝ, x ^ 12 + x ^ 11 + x ^ 10 - 5 * x ^ 9 + 3 * x ^ 8 - 7 * x ^ 3 + 7 ≥ 3 * x ^ 11 + 3 * x ^ 8 - 5 * x ^ 9 - 7 * x ^ 3 + 7 := by
  intro x
  nlinarith [mul_nonneg (sq_nonneg (x^5)) (sq_nonneg (x - 1))]
