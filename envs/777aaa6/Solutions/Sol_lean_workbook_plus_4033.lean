-- Prove2me | solution 1 for lean_workbook_plus_4033
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:34.471738+00:00
-- url     : https://prove2.me/submissions/d5d9c1c1-22e9-4c16-bfab-ccaaae68295f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hxy : x > y) (hy : y > 0) : x^4 + 3*y^4 > 4*x*y^3 := by
  have hx : 0 < x := lt_trans hy hxy
  have hp := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_gt hxy))) (show 0 < x^2+2*x*y+3*y^2 by positivity)
  nlinarith only [hp]
