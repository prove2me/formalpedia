-- Prove2me | solution 1 for lean_workbook_plus_78554
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:51.722712+00:00
-- url     : https://prove2.me/submissions/5227f038-5970-4cd1-bcfd-9e790388043e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b : ℝ) : (a + b) ^ 2 > 3 * (a + b - 1) := by
  nlinarith [sq_nonneg (a+b-3/2)]
