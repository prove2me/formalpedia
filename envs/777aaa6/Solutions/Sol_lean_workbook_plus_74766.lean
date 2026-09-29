-- Prove2me | solution 1 for lean_workbook_plus_74766
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:46.974715+00:00
-- url     : https://prove2.me/submissions/5088078c-5e8d-42bb-8127-f50e14b3ade7

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) :
  4 * (b^2 + b * c + c^2) * (a * b + b * c + c * a) ≤ (a * b + b * c + c * a + b^2 + b * c + c^2)^2 := by
  nlinarith [sq_nonneg (a*b+b*c+c*a-(b^2+b*c+c^2))]
