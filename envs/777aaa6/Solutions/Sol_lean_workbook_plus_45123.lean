-- Prove2me | solution 1 for lean_workbook_plus_45123
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:24:25.796397+00:00
-- url     : https://prove2.me/submissions/a60900f3-0017-4219-9f02-faeff39145d9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) : a / (a + 1) + 3 * b / (b + 1) + 3 * c / (c + 1) = 1 → a * b * c ≤ 1 / 120 := by
  clear habc
  intro h
  have hd₁ : 0 < a+1 := by positivity
  have hd₂ : 0 < b+1 := by positivity
  have hd₃ : 0 < c+1 := by positivity
  have hpoly : (3*a+2)*(b+c)+(6*a+5)*(b*c)=1 := by
    field_simp [ne_of_gt hd₁,ne_of_gt hd₂,ne_of_gt hd₃] at h
    nlinarith only [h]
  let u := Real.sqrt (b*c)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2=b*c := Real.sq_sqrt (mul_nonneg hb hc)
  have hs : 2*u ≤ b+c := by nlinarith only [hb,hc,hu,hu2,sq_nonneg (b-c)]
  have hm := mul_nonneg (show 0 ≤ 3*a+2 by positivity) (sub_nonneg.mpr hs)
  rw [←hu2] at hpoly
  have hg : 0 ≤ (1-(6*a+5)*u)*(1+u) := by nlinarith only [hpoly,hm]
  have hg1 := (mul_nonneg_iff_of_pos_right (show 0 < 1+u by positivity)).mp hg
  have hgu := mul_nonneg hu hg1
  have hbnd : a*u^2 ≤ (1:ℝ)/120 := by nlinarith only [hgu,sq_nonneg (10*u-1)]
  rw [hu2] at hbnd
  simpa only [mul_assoc] using hbnd
