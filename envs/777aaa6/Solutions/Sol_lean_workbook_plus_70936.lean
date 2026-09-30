-- Prove2me | solution 1 for lean_workbook_plus_70936
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:57:46.733015+00:00
-- url     : https://prove2.me/submissions/e9a06eb4-9c4a-4b30-95dd-494c00bbbd48

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

private theorem coordinate_bound (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (h : a*b*c = 3) : a ≤ 3 := by
  have hbc : 1 ≤ b*c := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  nlinarith only [h, mul_nonneg ha0 (sub_nonneg.mpr hbc)]

theorem solution (a b c : ℝ) (habc : a*b*c = 3)
    (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) :
    (a+1)*(b+1)*(c+1) ≥ 8*(a-1)*(b-1)*(c-1) := by
  have ha3 := coordinate_bound a b c ha hb hc habc
  have hb3 := coordinate_bound b c a hb hc ha (by nlinarith only [habc])
  have hc3 := coordinate_bound c a b hc ha hb (by nlinarith only [habc])
  have ha2 : 2*(a-1) ≤ a+1 := by linarith only [ha3]
  have hb2 : 2*(b-1) ≤ b+1 := by linarith only [hb3]
  have hc2 : 2*(c-1) ≤ c+1 := by linarith only [hc3]
  have hp := mul_le_mul ha2 hb2 (by linarith : 0 ≤ 2*(b-1))
    (by linarith : 0 ≤ a+1)
  have hq := mul_le_mul hp hc2 (by linarith : 0 ≤ 2*(c-1))
    (by positivity : 0 ≤ (a+1)*(b+1))
  nlinarith only [hq]
