-- Prove2me | solution 1 for lean_workbook_plus_38750
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:40.70457+00:00
-- url     : https://prove2.me/submissions/c27a5e79-7295-48c8-87ad-90138bec69c6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hxy : x > y) (hy : y > 0) : x^4 - y^4 > 4 * x * y^3 - 4 * y^4 := by
  have hx : 0 < x := lt_trans hy hxy
  have hp := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hxy))) (show 0 < x^2+2*x*y+3*y^2 by positivity)
  nlinarith only [hp]
