-- Prove2me | solution 1 for lean_workbook_plus_45475
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:49.488485+00:00
-- url     : https://prove2.me/submissions/3acc4245-de2a-4869-b8b0-7a18cc960811

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) (h : a^3 / b + 2 * b / a = 3) : a^2 + a * b + b^2 ≤ 3 := by
  have e1 : a^3 / b = a^4 := by
    rw [div_eq_iff hb.ne']
    linear_combination (-a^3) * hab
  have e2 : 2 * b / a = 2 * b^2 := by
    rw [div_eq_iff ha.ne']
    linear_combination (-2*b) * hab
  have h1 : a^4 + 2 * b^2 = 3 := by
    rw [e1, e2] at h
    exact h
  have h2 : (a^2 - 1)^2 * (a^2 + 2) = 0 := by
    linear_combination a^2 * h1 - 2 * (a*b + 1) * hab
  have h3 : (a^2 - 1)^2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · nlinarith [sq_nonneg a]
  have h4 : a^2 = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith
  have ha1 : a = 1 := by nlinarith
  have hb1 : b = 1 := by
    rw [ha1] at hab
    linarith
  rw [ha1, hb1]
  norm_num
