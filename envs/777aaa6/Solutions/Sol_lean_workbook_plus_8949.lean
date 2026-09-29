-- Prove2me | solution 1 for lean_workbook_plus_8949
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:20:20.835157+00:00
-- url     : https://prove2.me/submissions/3beeca17-c8ab-448a-928c-f00b41090e11

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : (1 / (1 + a^2) + 1 / (1 + b^2)) ≥ 2 / (1 + a * b) := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hab : 1 ≤ a*b := by nlinarith [mul_nonneg (show 0 ≤ a-1 by linarith) (show 0 ≤ b-1 by linarith)]
  have hd1 : 0 < 1+a^2 := by positivity
  have hd2 : 0 < 1+b^2 := by positivity
  have hd3 : 0 < 1+a*b := by linarith
  have he : 1/(1+a^2)+1/(1+b^2)-2/(1+a*b) = (a-b)^2*(a*b-1)/((1+a^2)*(1+b^2)*(1+a*b)) := by
    field_simp [ne_of_gt hd1, ne_of_gt hd2, ne_of_gt hd3]
    <;> ring
  have hp := div_nonneg (mul_nonneg (sq_nonneg (a-b)) (show 0 ≤ a*b-1 by linarith)) (le_of_lt (mul_pos (mul_pos hd1 hd2) hd3))
  linarith
