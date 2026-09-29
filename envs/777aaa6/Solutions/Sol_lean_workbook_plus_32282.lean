-- Prove2me | solution 1 for lean_workbook_plus_32282
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:51.437967+00:00
-- url     : https://prove2.me/submissions/62734dd4-a3b1-4e80-a878-f0decf5b1841

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a + b^2 + c ≤ a^2 + b^3 + c^2 := by
  have hp1 := mul_nonneg (sq_nonneg (a+b-2*c)) (show 0≤a+b+c/4 by positivity)
  have hp2 := mul_nonneg hc.le (sq_nonneg (a-b))
  have hs : 27≤(a+b+c)^3 := by nlinarith only [hp1,hp2,habc]
  have hs3 : 3≤a+b+c := by
    by_contra hn
    have hp := mul_neg_of_neg_of_pos (show a+b+c-3<0 by linarith) (show 0<(a+b+c)^2+3*(a+b+c)+9 by positivity)
    nlinarith only [hs,hp]
  have hbp := mul_nonneg (sq_nonneg (b-1)) (show 0≤b+1 by positivity)
  nlinarith only [hs3,hbp,sq_nonneg (a-1),sq_nonneg (c-1)]
