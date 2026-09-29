-- Prove2me | solution 1 for lean_workbook_plus_11411
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:07.066021+00:00
-- url     : https://prove2.me/submissions/73f83546-9379-475f-87f1-bac3f78ce1fc

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b c : ℝ, a^2 * b^2 + b^2 * c^2 + a^2 * c^2 - a * b^2 * c - a * b * c^2 - a^2 * b * c ≥ 0 := by
  intro a b c
  nlinarith [sq_nonneg (a*b-b*c), sq_nonneg (b*c-a*c), sq_nonneg (a*c-a*b)]
