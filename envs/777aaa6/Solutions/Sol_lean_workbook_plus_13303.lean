-- Prove2me | solution 1 for lean_workbook_plus_13303
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:49.402158+00:00
-- url     : https://prove2.me/submissions/ceb996a7-5ffd-4565-bc2e-960d4339206d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx: x ≥ 0) : Real.sqrt (3 + x^4) ≥ x + 1 := by
  apply Real.le_sqrt_of_sq_le
  have hp := mul_nonneg (sq_nonneg (x-1)) (show 0≤x^2+2*x+2 by nlinarith [sq_nonneg (x+1)])
  nlinarith only [hp]
