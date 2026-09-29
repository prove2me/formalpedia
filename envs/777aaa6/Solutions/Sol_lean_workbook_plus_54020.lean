-- Prove2me | solution 1 for lean_workbook_plus_54020
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:11:04.506353+00:00
-- url     : https://prove2.me/submissions/2e389ae4-ea9f-43fc-be50-acfdb07feee1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z a b c : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (a^2 / x + b^2 / y + c^2 / z) ≥ (a + b + c)^2 / (x + y + z) := by
  have hs : 0 < x+y+z := by linarith
  have h1 := mul_nonneg hz.le (sq_nonneg (a*y-b*x))
  have h2 := mul_nonneg hy.le (sq_nonneg (a*z-c*x))
  have h3 := mul_nonneg hx.le (sq_nonneg (b*z-c*y))
  have hn : 0 ≤ z*(a*y-b*x)^2+y*(a*z-c*x)^2+x*(b*z-c*y)^2 := by linarith
  have he : a^2/x+b^2/y+c^2/z-(a+b+c)^2/(x+y+z) = (z*(a*y-b*x)^2+y*(a*z-c*x)^2+x*(b*z-c*y)^2)/(x*y*z*(x+y+z)) := by
    field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz, ne_of_gt hs]
    <;> ring
  have hp := div_nonneg hn (show 0 ≤ x*y*z*(x+y+z) by positivity)
  linarith
