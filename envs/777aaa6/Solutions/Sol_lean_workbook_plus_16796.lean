-- Prove2me | solution 1 for lean_workbook_plus_16796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:43:24.223117+00:00
-- url     : https://prove2.me/submissions/53224c15-a0f5-49b0-a5e5-ce79c37ac15c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (ha : 0 < a) : (1 + a^2 + a^4)^4 ≥ 9 * a^4 * (a + a^2 + a^3)^2 := by
  have hf : 0 ≤ (a-1)^2*(a^2+a+1)*(a^4+a^3+3*a^2+a+1) := by positivity
  have hsmall : 0 ≤ (1+a^2+a^4)^2-3*a^2*(a+a^2+a^3) := by nlinarith only [hf]
  have hlarge := mul_nonneg hsmall
    (show 0 ≤ (1+a^2+a^4)^2+3*a^2*(a+a^2+a^3) by positivity)
  nlinarith only [hlarge]
