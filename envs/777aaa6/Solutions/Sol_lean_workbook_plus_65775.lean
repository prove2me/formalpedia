-- Prove2me | solution 1 for lean_workbook_plus_65775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:00.765473+00:00
-- url     : https://prove2.me/submissions/6a49bb2e-5df1-4980-9375-5ada55a0f02b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : 0 < x) : (x^2 + 1)^2 * (x^4 - x^3 + x^2 - x + 1)^2 > 0 := by
  have hq : 0 < x^4-x^3+x^2-x+1 := by
    nlinarith [sq_nonneg (x^2-x/2), sq_nonneg (x-1), sq_nonneg x]
  exact mul_pos (sq_pos_of_pos (by positivity)) (sq_pos_of_pos hq)
