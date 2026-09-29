-- Prove2me | solution 1 for lean_workbook_plus_16358
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:15:32.44601+00:00
-- url     : https://prove2.me/submissions/cb8d96ae-9c81-418a-8024-42216991eeec

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a + b = 1) : 1 / 3 ≤ a ^ 2 / (a + 1) + b ^ 2 / (b + 1) ∧ a ^ 2 / (a + 1) + b ^ 2 / (b + 1) < 1 / 2 := by
  have hda : 0 < a+1 := by linarith
  have hdb : 0 < b+1 := by linarith
  have hl : a^2/(a+1)+b^2/(b+1)-1/3 = (a-b)^2/(3*(a+1)*(b+1)) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb]
    linear_combination (3*a*b+2*a+2*b+1)*hab
  have hu : 1/2-(a^2/(a+1)+b^2/(b+1)) = 3*a*b/(2*(a+1)*(b+1)) := by
    field_simp [ne_of_gt hda, ne_of_gt hdb]
    linear_combination -(2*a*b+2*a+2*b+1)*hab
  have hn : 0 ≤ (a-b)^2/(3*(a+1)*(b+1)) := div_nonneg (sq_nonneg _) (by positivity)
  have hp : 0 < 3*a*b/(2*(a+1)*(b+1)) := by positivity
  constructor <;> linarith
