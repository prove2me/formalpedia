-- Prove2me | solution 1 for lean_workbook_plus_38747
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:41.819167+00:00
-- url     : https://prove2.me/submissions/36be2ab2-da66-4839-bce6-85b8f6a3b377

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : x^5 - x^3 + x - 17 = 0) : 4 < x^3 ∧ x^3 < 17 := by
  have hq : 0 < x^4 - x^2 + 1 := by nlinarith [sq_nonneg (x^2 - 1/2)]
  have hxpos : 0 < x := by
    by_contra hneg
    push_neg at hneg
    have : x * (x^4 - x^2 + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hq.le
    nlinarith
  constructor
  · by_contra hle
    push_neg at hle
    have hx16 : x ≤ 1.6 := by nlinarith [sq_nonneg (x - 1.6), sq_nonneg x, mul_pos hxpos hxpos]
    nlinarith [mul_nonneg hxpos.le hq.le, mul_nonneg (mul_nonneg hxpos.le hxpos.le) (sub_nonneg.mpr hx16), sq_nonneg x]
  · by_contra hge
    push_neg at hge
    have hx25 : x ≥ 2.5 := by nlinarith [sq_nonneg (x - 2.5), sq_nonneg x, mul_pos hxpos hxpos]
    nlinarith [mul_nonneg hxpos.le hq.le, mul_nonneg (mul_nonneg hxpos.le hxpos.le) (sub_nonneg.mpr hx25), sq_nonneg x]
