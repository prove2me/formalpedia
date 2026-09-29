-- Prove2me | solution 1 for lean_workbook_plus_18200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:51:56.627371+00:00
-- url     : https://prove2.me/submissions/779c3a42-137f-4964-b6ba-4e69dc6f6789

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (b : ℝ) (h : b >= 0) : 13*b^3 - 5*b^2 - 8*b + 4 >= 0 := by
  have hp := mul_nonneg (sq_nonneg (b-3/5)) (show 0 ≤ 13*b+53/5 by linarith)
  nlinarith
