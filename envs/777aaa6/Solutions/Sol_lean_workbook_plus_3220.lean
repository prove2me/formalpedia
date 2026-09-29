-- Prove2me | solution 1 for lean_workbook_plus_3220
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:10:39.641359+00:00
-- url     : https://prove2.me/submissions/f7fff96e-3916-4ff7-bccf-82937ca54b5b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (a : ℝ) (h : 0 < a ∧ a < 2) : a < Real.sqrt (2 * a) ∧ Real.sqrt (2 * a) < 2 := by
  constructor
  · exact (Real.lt_sqrt h.1.le).2 (by nlinarith [h.1, h.2])
  · exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)).2 (by linarith [h.2])
