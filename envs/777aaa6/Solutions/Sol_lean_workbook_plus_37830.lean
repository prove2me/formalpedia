-- Prove2me | solution 1 for lean_workbook_plus_37830
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:32:41.945132+00:00
-- url     : https://prove2.me/submissions/5a2f66bc-195c-4cc5-9c6e-169cc2042574

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : |x - 4| < 1) : 1 / |x + 4| ≤ 1 / 7 := by
  have hx' := abs_lt.mp hx
  have hpos : 0 < x+4 := by linarith
  rw [abs_of_pos hpos]
  apply (div_le_div_iff₀ hpos (by norm_num : (0:ℝ)<7)).2
  linarith
