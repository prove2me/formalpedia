-- Prove2me | solution 1 for lean_workbook_plus_11044
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:44.054469+00:00
-- url     : https://prove2.me/submissions/b8fff82a-d5ef-4f48-9e46-2d214e90cb34

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (h₁ : x ^ 4 + y ^ 4 < 4) (h₂ : x ^ 3 + y ^ 3 > 3) : x ^ 2 + y ^ 2 > 2 := by
  have hq0 : 0 ≤ x^2 + y^2 := by positivity
  have hcs : (x^3+y^3)^2 ≤ (x^4+y^4)*(x^2+y^2) := by nlinarith [sq_nonneg (x^2*y-x*y^2)]
  have hsq : 9 < (x^3+y^3)^2 := by nlinarith only [h₂, sq_nonneg (x^3+y^3-3)]
  by_contra hbad
  have hq : x^2+y^2 ≤ 2 := le_of_not_gt hbad
  have hprod : (x^4+y^4)*(x^2+y^2) ≤ 8 := calc
    _ ≤ 4*(x^2+y^2) := mul_le_mul_of_nonneg_right (le_of_lt h₁) hq0
    _ ≤ 4*2 := mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = 8 := by norm_num
  linarith only [hcs, hsq, hprod]
