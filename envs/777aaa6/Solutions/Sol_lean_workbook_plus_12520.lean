-- Prove2me | solution 1 for lean_workbook_plus_12520
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:32.61046+00:00
-- url     : https://prove2.me/submissions/7b1a834e-e5af-4146-b6cd-f76850fbfbb1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a^4 * b^2 * c^2 + a^2 * b^4 * c^2 + a^2 * b^2 * c^4 ≤ a^4 * b^4 + b^4 * c^4 + c^4 * a^4 := by
  nlinarith [sq_nonneg (a^2*b^2-b^2*c^2),sq_nonneg (b^2*c^2-c^2*a^2),sq_nonneg (c^2*a^2-a^2*b^2)]
