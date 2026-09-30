-- Prove2me | solution 1 for lean_workbook_plus_40812
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:12:26.16796+00:00
-- url     : https://prove2.me/submissions/990e44bd-d58f-4429-8825-509005d9bedb

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a = a^2 / (a * b) + b^2 / (b * c) + c^2 / (c * a) ∧ a / b + b / c + c / a ≥ (a + b + c)^2 / (a * b + b * c + c * a) := by
  have hab : a * b ≠ 0 := by positivity
  have hbc : b * c ≠ 0 := by positivity
  have hca : c * a ≠ 0 := by positivity
  constructor
  · field_simp
  · have key : a / b + b / c + c / a = (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) / (a * b * c) := by
      field_simp
    rw [key, ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg a) hb.le) (sq_nonneg (b - c)),
      mul_nonneg (mul_nonneg ha.le (sq_nonneg c)) (sq_nonneg (a - b)),
      mul_nonneg (mul_nonneg (sq_nonneg b) hc.le) (sq_nonneg (c - a))]
