-- Prove2me | solution 1 for lean_workbook_plus_32961
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:31:36.265315+00:00
-- url     : https://prove2.me/submissions/8e761f4d-776e-4498-b052-6cbb6c6af2dd

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) (hf : 0 < f) : (a * b / (a + b) + c * d / (c + d) + e * f / (e + f)) ≤ (a + c + e) * (b + d + f) / (a + b + c + d + e + f) := by
  have hs1 : 0 < a+b := by linarith
  have hs2 : 0 < c+d := by linarith
  have hs3 : 0 < e+f := by linarith
  have hs : 0 < a+b+c+d+e+f := by linarith
  have h1 := mul_nonneg hs3.le (sq_nonneg (a*d-b*c))
  have h2 := mul_nonneg hs2.le (sq_nonneg (a*f-b*e))
  have h3 := mul_nonneg hs1.le (sq_nonneg (c*f-d*e))
  have hId : (a+c+e)*(b+d+f)/(a+b+c+d+e+f)-
      (a*b/(a+b)+c*d/(c+d)+e*f/(e+f)) =
      ((e+f)*(a*d-b*c)^2+(c+d)*(a*f-b*e)^2+(a+b)*(c*f-d*e)^2)/
      ((a+b)*(c+d)*(e+f)*(a+b+c+d+e+f)) := by
    field_simp [ne_of_gt hs1,ne_of_gt hs2,ne_of_gt hs3,ne_of_gt hs]
    <;> ring
  have hn : 0 ≤ ((e+f)*(a*d-b*c)^2+(c+d)*(a*f-b*e)^2+(a+b)*(c*f-d*e)^2)/
      ((a+b)*(c+d)*(e+f)*(a+b+c+d+e+f)) :=
    div_nonneg (by linarith) (by positivity)
  linarith
