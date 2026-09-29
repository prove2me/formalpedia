-- Prove2me | solution 1 for lean_workbook_plus_68120
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:59.624942+00:00
-- url     : https://prove2.me/submissions/094abb78-a2c8-4e4d-a5f0-2ed975777fe4

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) : a^2*c^2 - a*b*c*d + b^2*d^2 ≥ a*b*c*d := by
  nlinarith [sq_nonneg (a*c-b*d)]
