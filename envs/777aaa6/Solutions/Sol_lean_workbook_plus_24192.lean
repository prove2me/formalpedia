-- Prove2me | solution 1 for lean_workbook_plus_24192
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:40:24.669158+00:00
-- url     : https://prove2.me/submissions/2958bc70-da67-426d-aa8c-9eeba7c0f4ce

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (hab : a * b + b * c + c * a > 0) : (1 / (a ^ 2 + b ^ 2 + c ^ 2)) * ((a - b) ^ 2 * (a + b - Real.sqrt 3 * c) ^ 2 / (a + c) / (b + c) + (b - c) ^ 2 * (b + c - Real.sqrt 3 * a) ^ 2 / (b + a) / (c + a) + (c - a) ^ 2 * (c + a - Real.sqrt 3 * b) ^ 2 / (c + b) / (a + b)) ≥ 0 := by
  have d1 : (a + c) * (b + c) > 0 := by nlinarith [sq_nonneg c]
  have d2 : (b + a) * (c + a) > 0 := by nlinarith [sq_nonneg a]
  have d3 : (c + b) * (a + b) > 0 := by nlinarith [sq_nonneg b]
  apply mul_nonneg
  · positivity
  · rw [div_div, div_div, div_div]
    have t1 : (a - b) ^ 2 * (a + b - Real.sqrt 3 * c) ^ 2 / ((a + c) * (b + c)) ≥ 0 :=
      div_nonneg (by positivity) d1.le
    have t2 : (b - c) ^ 2 * (b + c - Real.sqrt 3 * a) ^ 2 / ((b + a) * (c + a)) ≥ 0 :=
      div_nonneg (by positivity) d2.le
    have t3 : (c - a) ^ 2 * (c + a - Real.sqrt 3 * b) ^ 2 / ((c + b) * (a + b)) ≥ 0 :=
      div_nonneg (by positivity) d3.le
    linarith
