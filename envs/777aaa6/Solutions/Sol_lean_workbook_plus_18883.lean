-- Prove2me | solution 1 for lean_workbook_plus_18883
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:01.834296+00:00
-- url     : https://prove2.me/submissions/699fe8ac-acd0-44fc-b9b5-b5b9fcd8aff1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x^6 - x^4 + 2*x^3 - x^2 - 6*x + 5 ≥ 0 := by
  have hp := mul_nonneg (sq_nonneg (x-1)) (sq_nonneg (x^2+x))
  have hq := mul_nonneg (sq_nonneg (x-1)) (sq_nonneg (x+2))
  nlinarith only [hp,hq,sq_nonneg (x-1)]
