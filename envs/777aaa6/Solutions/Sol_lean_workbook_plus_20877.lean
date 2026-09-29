-- Prove2me | solution 1 for lean_workbook_plus_20877
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:07:09.919778+00:00
-- url     : https://prove2.me/submissions/cfc5bcd7-4062-4e18-88c4-56acc2a3f5f0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a / (b + 1) + b / (c + 1) + c / (a + 1) = 1) : a * b * c ≤ 1 / 8 := by
  clear habc
  have hd₁ : 0 < a+1 := by positivity
  have hd₂ : 0 < b+1 := by positivity
  have hd₃ : 0 < c+1 := by positivity
  have he : (a/(b+1)+b/(c+1)+c/(a+1))*(a*(b+1)+b*(c+1)+c*(a+1))-(a+b+c)^2 = a*b*(b-c)^2/((b+1)*(c+1))+b*c*(c-a)^2/((c+1)*(a+1))+c*a*(a-b)^2/((a+1)*(b+1)) := by
    field_simp [ne_of_gt hd₁,ne_of_gt hd₂,ne_of_gt hd₃] <;> ring
  rw [h] at he
  have hterms : 0 ≤ a*b*(b-c)^2/((b+1)*(c+1))+b*c*(c-a)^2/((c+1)*(a+1))+c*a*(a-b)^2/((a+1)*(b+1)) := by positivity
  have hC : (a+b+c)^2 ≤ (a+b+c)+(a*b+b*c+c*a) := by nlinarith only [he,hterms]
  have hQ : 3*(a*b+b*c+c*a) ≤ (a+b+c)^2 := by nlinarith only [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have hf : 0 ≤ (3-2*(a+b+c))*(a+b+c) := by nlinarith only [hC,hQ]
  have hs0 : 0 < a+b+c := by positivity
  have hsl := (mul_nonneg_iff_of_pos_right hs0).mp hf
  have hs : a+b+c ≤ (3:ℝ)/2 := by linarith only [hsl]
  have hA : 27*a*b*c ≤ (a+b+c)^3 := by
    nlinarith only [mul_nonneg (sq_nonneg (a+b-2*c)) (show 0 ≤ a+b+c/4 by positivity), mul_nonneg (le_of_lt hc) (sq_nonneg (a-b))]
  have hfactor := mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ (a+b+c)^2+((3:ℝ)/2)*(a+b+c)+((3:ℝ)/2)^2 by positivity)
  nlinarith only [hA,hfactor]
