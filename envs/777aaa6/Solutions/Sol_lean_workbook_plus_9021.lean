-- Prove2me | solution 1 for lean_workbook_plus_9021
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:30.021917+00:00
-- url     : https://prove2.me/submissions/00da5081-afa1-4f2c-a238-ed70ec7205a6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c x y z : ℝ) :
  (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2) ≥ (a * x + b * y + c * z)^2 := by
  nlinarith [sq_nonneg (a*y-b*x),sq_nonneg (a*z-c*x),sq_nonneg (b*z-c*y)]
