-- Prove2me | solution 1 for lean_workbook_plus_45201
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:06:18.711606+00:00
-- url     : https://prove2.me/submissions/9b628ea3-96a4-4e90-9b55-79377001a94d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 80000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * (b + 1)) + 1 / (b * (c + 1)) + 1 / (c * (a + 1))) ≥ 3 / (1 + a * b * c) := by
  have hp : 0 < 1 + a*b*c := by positivity
  have hD : 0 < a*b*c*(a+1)*(b+1)*(c+1)*(1+a*b*c) := by positivity
  have hidentity :
      (1/(a*(b+1)) + 1/(b*(c+1)) + 1/(c*(a+1)) - 3/(1+a*b*c)) *
        (a*b*c*(a+1)*(b+1)*(c+1)*(1+a*b*c)) =
      c*(a-a*b*c)^2 + b*(a*b*c-c)^2 + (b*c)*(1-a*b)^2 +
        a*(a*b*c-b)^2 + (a*c)*(1-b*c)^2 + (a*b)*(1-a*c)^2 := by
    field_simp
    <;> ring
  have hsum : 0 ≤ c*(a-a*b*c)^2 + b*(a*b*c-c)^2 + (b*c)*(1-a*b)^2 +
      a*(a*b*c-b)^2 + (a*c)*(1-b*c)^2 + (a*b)*(1-a*c)^2 := by positivity
  have hproduct : 0 ≤
      (1/(a*(b+1)) + 1/(b*(c+1)) + 1/(c*(a+1)) - 3/(1+a*b*c)) *
        (a*b*c*(a+1)*(b+1)*(c+1)*(1+a*b*c)) := by rw [hidentity]; exact hsum
  have hgap := nonneg_of_mul_nonneg_left hproduct hD
  linarith only [hgap]
