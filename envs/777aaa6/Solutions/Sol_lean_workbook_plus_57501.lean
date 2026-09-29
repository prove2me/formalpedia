-- Prove2me | solution 1 for lean_workbook_plus_57501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:44.909004+00:00
-- url     : https://prove2.me/submissions/c9da79e3-f04f-44dd-90bc-4562e3cc5076

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : (a^3 + b^3)^2 ≤ (a^2 + b^2)^3 := by
  nlinarith [sq_nonneg (a^2*b-a*b^2),sq_nonneg (a^2*b),sq_nonneg (a*b^2)]
