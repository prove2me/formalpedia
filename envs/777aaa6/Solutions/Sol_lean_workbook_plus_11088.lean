-- Prove2me | solution 1 for lean_workbook_plus_11088
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:27:49.063088+00:00
-- url     : https://prove2.me/submissions/39ac55a9-11ec-4d81-a852-be8ac50c7844

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (x : ℝ) (hx : x ≥ 0) : (x^2 + 1)^6 / 2^7 + 1 / 2 ≥ x^5 - x^3 + x := by
  have hb : 2*x ≤ x^2+1 := by nlinarith [sq_nonneg (x-1)]
  have hp : (2*x)^6 ≤ (x^2+1)^6 := pow_le_pow_left₀ (by positivity) hb 6
  have hq : 0 ≤ x^4-x^2+1 := by nlinarith [sq_nonneg (x^2-1/2)]
  have hs := mul_nonneg (sq_nonneg (x-1)) hq
  nlinarith only [hp,hs]
