-- Prove2me | solution 1 for lean_workbook_plus_46461
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:54.097739+00:00
-- url     : https://prove2.me/submissions/5edee4ee-3bd4-494f-8932-0425c8be3164

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a^2 - a + 1) * (b^3 + 1) ≥ (a^2 + b) * (b^2 + 1) := by
  have hA : 0<2*b^3-b^2+1 := by
    by_cases hb1 : b≤1
    · have hs : b^2≤1 := by simpa using pow_le_pow_left₀ hb.le hb1 2
      nlinarith [pow_pos hb 3]
    · have hp := mul_pos (sq_pos_of_pos hb) (show 0<2*b-1 by linarith)
      nlinarith only [hp]
  have hQ : 0≤b^4+b^3-b^2+b+1 := by nlinarith [sq_nonneg (b^2-1/2),pow_pos hb 3]
  have hp := mul_nonneg (sq_nonneg (b-1)) hQ
  have hs := sq_nonneg ((2*b^3-b^2+1)*a-(b^3+1))
  have he : 0≤(2*b^3-b^2+1)*(2*(a^2-a+1)*(b^3+1)-(a^2+b)*(b^2+1)) := by nlinarith only [hp,hs]
  have hd := nonneg_of_mul_nonneg_right he hA
  linarith only [hd]
