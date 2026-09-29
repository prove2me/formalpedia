-- Prove2me | solution 1 for lean_workbook_plus_61076
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:24:23.127891+00:00
-- url     : https://prove2.me/submissions/c205be75-799a-40bb-a390-97779cf4518c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) : a / (a + 1) + 2 * b / (b + 1) + 2 * c / (c + 1) = 1 → a * b * c ≤ 1 / 48 := by
  clear habc
  intro h
  have hd₁ : 0 < a+1 := by positivity
  have hd₂ : 0 < b+1 := by positivity
  have hd₃ : 0 < c+1 := by positivity
  have hpoly : (2*a+1)*(b+c)+(4*a+3)*(b*c)=1 := by
    field_simp [ne_of_gt hd₁,ne_of_gt hd₂,ne_of_gt hd₃] at h
    nlinarith only [h]
  let u := Real.sqrt (b*c)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2=b*c := Real.sq_sqrt (mul_nonneg hb hc)
  have hs : 2*u ≤ b+c := by nlinarith only [hb,hc,hu,hu2,sq_nonneg (b-c)]
  have hm := mul_nonneg (show 0 ≤ 2*a+1 by positivity) (sub_nonneg.mpr hs)
  rw [←hu2] at hpoly
  have hg : 0 ≤ (1-(4*a+3)*u)*(1+u) := by nlinarith only [hpoly,hm]
  have hg1 := (mul_nonneg_iff_of_pos_right (show 0 < 1+u by positivity)).mp hg
  have hgu := mul_nonneg hu hg1
  have hbnd : a*u^2 ≤ (1:ℝ)/48 := by nlinarith only [hgu,sq_nonneg (6*u-1)]
  rw [hu2] at hbnd
  simpa only [mul_assoc] using hbnd
