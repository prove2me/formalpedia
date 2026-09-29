-- Prove2me | solution 1 for lean_workbook_plus_40026
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:09.792411+00:00
-- url     : https://prove2.me/submissions/316ba2fe-20a3-426c-86c5-83281c545e11

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a + b + c + d = 1) : a * b + b * c + c * d ≤ 1 / 4 := by
  have hp := mul_nonneg ha.le hd.le
  have he : (a+b+c+d)^2 = 1 := by rw [habc]; norm_num
  nlinarith [sq_nonneg (a+c-b-d)]
