-- Prove2me | solution 1 for lean_workbook_plus_72135
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:09:26.832242+00:00
-- url     : https://prove2.me/submissions/3adf79cc-e56e-4818-9b49-af3709c6e9cc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  (x + y) / (x + y + 2 * z) + (y + z) / (y + z + 2 * x) + (z + x) / (z + x + 2 * y) < 2 := by
  have hx : 0 < x := h₀.1
  have hy : 0 < y := h₀.2.1
  have hz : 0 < z := h₀.2.2
  have hd1 : 0 < x+y+2*z := by positivity
  have hd2 : 0 < y+z+2*x := by positivity
  have hd3 : 0 < z+x+2*y := by positivity
  have hn : 0 < 3*(x^2*y+x^2*z+y^2*x+y^2*z+z^2*x+z^2*y)+14*x*y*z := by positivity
  have he : 2-((x+y)/(x+y+2*z)+(y+z)/(y+z+2*x)+(z+x)/(z+x+2*y)) = (3*(x^2*y+x^2*z+y^2*x+y^2*z+z^2*x+z^2*y)+14*x*y*z)/((x+y+2*z)*(y+z+2*x)*(z+x+2*y)) := by
    field_simp [ne_of_gt hd1, ne_of_gt hd2, ne_of_gt hd3]
    <;> ring
  have hp := div_pos hn (mul_pos (mul_pos hd1 hd2) hd3)
  linarith
