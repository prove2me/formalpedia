-- Prove2me | solution 1 for lean_workbook_plus_31326
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:23.958715+00:00
-- url     : https://prove2.me/submissions/6834d878-7721-44e0-a661-7806a084b03d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x a : ℝ) (h : x^5 - x^3 + x = a) :
  (x - 1)^2 * (x^2 + x * Real.sqrt 3 + 1) * (x^2 - x * Real.sqrt 3 + 1) ≥ 0 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ x^2 + x*Real.sqrt 3 + 1 := by
    nlinarith [sq_nonneg (x + Real.sqrt 3 / 2)]
  have hm : 0 ≤ x^2 - x*Real.sqrt 3 + 1 := by
    nlinarith [sq_nonneg (x - Real.sqrt 3 / 2)]
  exact mul_nonneg (mul_nonneg (sq_nonneg (x-1)) hp) hm
