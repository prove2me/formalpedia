-- Prove2me | solution 1 for lean_workbook_plus_43590
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:26.031827+00:00
-- url     : https://prove2.me/submissions/f26b182a-4082-4afc-9208-3648db179c26

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^4 = 5) : a + b ≤ 3 := by
  have hp := mul_nonneg (sq_nonneg (b-1)) (show 0 ≤ b^2+2*b+3 by positivity)
  nlinarith [sq_nonneg (a-2)]
