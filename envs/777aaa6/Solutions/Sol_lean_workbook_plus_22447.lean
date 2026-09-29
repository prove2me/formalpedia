-- Prove2me | solution 1 for lean_workbook_plus_22447
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:03.038612+00:00
-- url     : https://prove2.me/submissions/916d42eb-dabb-4058-9346-1825c18878bd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : a + b >= 2) : a^4 + b^4 >= a^3 + b^3 := by
  have hs : 0≤a+b := by linarith
  have hm : 0≤a+b-1 := by linarith
  have hp := mul_nonneg (pow_nonneg hs 3) (show 0≤a+b-2 by linarith)
  have hq := mul_nonneg (mul_nonneg hs hm) (sq_nonneg (a-b))
  nlinarith only [hp,hq,sq_nonneg ((a-b)^2)]
