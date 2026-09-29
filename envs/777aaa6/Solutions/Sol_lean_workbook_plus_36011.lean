-- Prove2me | solution 1 for lean_workbook_plus_36011
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:20.513375+00:00
-- url     : https://prove2.me/submissions/f6630661-a6fa-4482-816f-f1d5c72e1516

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a - b) ^ 2 / (2 * a * b + 1) + (2 * a * b - 1) / (a ^ 2 + b ^ 2 + 1) ≥ (a ^ 2 + b ^ 2 - 1) / (a + b) ^ 2 := by
  have hd1 : 0 < 2*a*b+1 := by positivity
  have hd2 : 0 < a^2+b^2+1 := by positivity
  have hd3 : 0 < (a+b)^2 := by positivity
  have h1 := mul_nonneg (sq_nonneg ((a^2+b^2)-2*a*b)) (show 0 ≤ 2*(a^2+b^2)+2*a*b by positivity)
  have h2 := mul_nonneg (sq_nonneg (2*a*b-1)) (show 0 ≤ 4*a*b+1 by positivity)
  have h3 := mul_nonneg (sq_nonneg (1-(a^2+b^2))) (show 0 ≤ 2+(a^2+b^2) by positivity)
  have hn : 0 ≤ (a^2+b^2)^3+(2*a*b)^3+1-(2*a*b)*(a^2+b^2)^2-(2*a*b)^2-(a^2+b^2) := by nlinarith only [h1,h2,h3]
  have he : (a-b)^2/(2*a*b+1)+(2*a*b-1)/(a^2+b^2+1)-(a^2+b^2-1)/(a+b)^2 = ((a^2+b^2)^3+(2*a*b)^3+1-(2*a*b)*(a^2+b^2)^2-(2*a*b)^2-(a^2+b^2))/((a+b)^2*(2*a*b+1)*(a^2+b^2+1)) := by
    field_simp [ne_of_gt hd1, ne_of_gt hd2, ne_of_gt hd3]
    <;> ring
  have hp := div_nonneg hn (show 0 ≤ (a+b)^2*(2*a*b+1)*(a^2+b^2+1) by positivity)
  linarith
