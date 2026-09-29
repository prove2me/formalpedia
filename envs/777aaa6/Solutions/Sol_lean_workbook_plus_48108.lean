-- Prove2me | solution 1 for lean_workbook_plus_48108
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:24:21.420593+00:00
-- url     : https://prove2.me/submissions/72dc4346-4c16-4233-bbf6-0976e224db7f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (x : ℝ) : x^4 - x^3 + x^2 - x + 1 / 3 > 0 := by
  by_cases hx : x = 2/3
  · subst x
    norm_num
  · have hpos : 0 < (x-2/3)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hx)
    nlinarith [sq_nonneg (x^2-x/2)]
