-- Prove2me | solution 1 for lean_workbook_plus_47390
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:13.12844+00:00
-- url     : https://prove2.me/submissions/2b23e8c7-385c-4e2e-b106-59dc375680d8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) : (a+b)^2 + (3 * Real.sqrt (a * b))^2 >= 6 * (a + b) * Real.sqrt (a * b) := by
  nlinarith [sq_nonneg (a+b-3*Real.sqrt (a*b))]
