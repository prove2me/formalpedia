-- Prove2me | solution 1 for lean_workbook_plus_12651
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:29:17.153181+00:00
-- url     : https://prove2.me/submissions/c8d171e5-dfba-4cba-8d1f-c202f4893c43

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c : ℝ) : (a^2+1)*(b^2+1)*(c^2+1) ≥ (a+b+c-a*b*c)^2 := by
  nlinarith [sq_nonneg (a*b+b*c+c*a-1)]
