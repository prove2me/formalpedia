-- Prove2me | solution 1 for lean_workbook_plus_35488
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:53.152124+00:00
-- url     : https://prove2.me/submissions/8a894074-4192-4594-854b-3d791890f199

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (h : a^2 - 34*a + 240 = 0) : a = 10 ∨ a = 24 := by
  have hp : (a-10)*(a-24) = 0 := by nlinarith
  rcases mul_eq_zero.mp hp with h | h
  · left; linarith
  · right; linarith
