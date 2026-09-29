-- Prove2me | solution 1 for lean_workbook_plus_36869
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:59.419586+00:00
-- url     : https://prove2.me/submissions/846dab60-d7eb-4306-a62d-226e3d9bd8e1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ x : ℝ, x^6 - 6 * x + 5 ≥ 0 := by
  intro x
  by_cases hx : 0 ≤ x
  · have hp : 0 ≤ x^4+2*x^3+3*x^2+4*x+5 := by positivity
    nlinarith [mul_nonneg (sq_nonneg (x-1)) hp]
  · nlinarith [sq_nonneg (x^3)]
