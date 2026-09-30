-- Prove2me | solution 1 for lean_workbook_plus_41314
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:02.608558+00:00
-- url     : https://prove2.me/submissions/46365b3e-7c16-48e3-8e6c-49ee7a63d670

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^3 + b^2 ≥ a^4 + b^3) : a^3 + b^3 ≤ 4 := by
  -- b^2 - b^3 ≤ 4/27  and  a^3 - a^4 ≤ 27/256
  have hb27 : 27 * b ^ 3 - 27 * b ^ 2 + 4 ≥ 0 := by
    nlinarith [mul_nonneg (sq_nonneg (3 * b - 2)) (by linarith : (0:ℝ) ≤ 3 * b + 1)]
  have ha256 : 256 * a ^ 4 - 256 * a ^ 3 + 27 ≥ 0 := by
    nlinarith [mul_nonneg (sq_nonneg (4 * a - 3)) (by positivity : (0:ℝ) ≤ 16 * a ^ 2 + 8 * a + 3)]
  have ha1 : a ≤ 5 / 4 := by
    by_contra h
    push_neg at h
    have h2 : a ^ 2 > 25 / 16 := by nlinarith
    have h3 : a ^ 3 > 125 / 64 := by nlinarith
    have h4 : a ^ 4 - a ^ 3 > 125 / 256 := by
      have : a ^ 4 - a ^ 3 = a ^ 3 * (a - 1) := by ring
      rw [this]
      nlinarith [mul_lt_mul_of_pos_right h3 (by linarith : (0:ℝ) < a - 1)]
    nlinarith
  have hb1 : b ≤ 5 / 4 := by
    by_contra h
    push_neg at h
    have h2 : b ^ 2 > 25 / 16 := by nlinarith
    have h4 : b ^ 3 - b ^ 2 > 25 / 64 := by
      have : b ^ 3 - b ^ 2 = b ^ 2 * (b - 1) := by ring
      rw [this]
      nlinarith [mul_lt_mul_of_pos_right h2 (by linarith : (0:ℝ) < b - 1)]
    nlinarith
  have ha3 : a ^ 3 ≤ (5/4) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (by positivity : (0:ℝ) ≤ (5/4)^2 + 5/4 * a + a^2)]
  have hb3 : b ^ 3 ≤ (5/4) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (by positivity : (0:ℝ) ≤ (5/4)^2 + 5/4 * b + b^2)]
  nlinarith
