-- Prove2me | solution 1 for lean_workbook_plus_33338
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:55.946228+00:00
-- url     : https://prove2.me/submissions/96932bb1-45ce-4ebd-a376-c85b1f6a44fb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : 4*x+3 = 12*x^2 + 7*x) : x = (-1 + Real.sqrt 17)/8 ∨ x = (-1 - Real.sqrt 17)/8 := by
  have hs : (Real.sqrt 17)^2 = 17 := Real.sq_sqrt (by norm_num)
  have he : (8*x+1-Real.sqrt 17)*(8*x+1+Real.sqrt 17) = 0 := by nlinarith
  rcases mul_eq_zero.mp he with h | h
  · left; linarith
  · right; linarith
