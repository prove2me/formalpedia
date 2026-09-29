-- Prove2me | solution 1 for lean_workbook_plus_66781
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:58.50417+00:00
-- url     : https://prove2.me/submissions/f1cb6099-a9d4-46df-be3a-d31157b30657

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (h : a < b) (h1 : 0 < a) : a^3 - 3*a - 2 ≤ b^3 - 3*b + 2 := by
  by_cases ha2 : a≤2
  · have hp := mul_nonpos_of_nonpos_of_nonneg (show a-2≤0 by linarith) (sq_nonneg (a+1))
    have hq := mul_nonneg (sq_nonneg (b-1)) (show 0≤b+2 by linarith)
    nlinarith only [hp,hq]
  · have hb : 0<b := lt_trans h1 h
    have hq : 0≤a^2+a*b+b^2-3 := by nlinarith [sq_nonneg (a-2),mul_pos h1 hb,sq_nonneg b]
    have hp := mul_nonneg (show 0≤b-a by linarith) hq
    nlinarith only [hp]
