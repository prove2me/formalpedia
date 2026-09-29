-- Prove2me | solution 1 for lean_workbook_plus_56308
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:03.111831+00:00
-- url     : https://prove2.me/submissions/7acba606-e031-4bc5-8dc3-5533e98db122

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c d : ℝ) : (a * b * c + b * c * d + c * d * a + d * a * b) ^ 2 / (3 * (a * b * c + b * c * d + c * d * a + d * a * b)) = (a * b * c + b * c * d + c * d * a + d * a * b) / 3 := by
  set s := a*b*c+b*c*d+c*d*a+d*a*b
  change s^2 / (3*s) = s/3
  by_cases hs : s=0
  · simp [hs]
  · field_simp
