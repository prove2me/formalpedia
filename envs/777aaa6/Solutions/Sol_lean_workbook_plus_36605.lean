-- Prove2me | solution 1 for lean_workbook_plus_36605
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:53.058681+00:00
-- url     : https://prove2.me/submissions/14afcdc2-0daf-4a44-bb65-df6859f3da8f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ b c : ℝ, b^2 * c^2 + b^2 + 1 ≥ b + b^2 * c + b * c := by
  intro b c
  nlinarith [sq_nonneg (b*c-b),sq_nonneg (b-1),sq_nonneg (b*c-1)]
