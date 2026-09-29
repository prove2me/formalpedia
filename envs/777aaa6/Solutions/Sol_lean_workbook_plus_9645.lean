-- Prove2me | solution 1 for lean_workbook_plus_9645
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:42:33.127132+00:00
-- url     : https://prove2.me/submissions/5f242281-e022-4807-bb52-336176ce455c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (h : a * c + b * d = 0) :
  (a + b + c + d) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 2) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (a+c-b-d)]
