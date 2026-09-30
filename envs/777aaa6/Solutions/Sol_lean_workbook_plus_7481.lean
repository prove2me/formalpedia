-- Prove2me | solution 1 for lean_workbook_plus_7481
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:21:49.362822+00:00
-- url     : https://prove2.me/submissions/e755ebc2-ca93-4660-a94b-adc2b994ece9

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) (hab : x*y*z = (1 - x)*(1 - y)*(1 - z)) : (1 - x)*y ≥ 1/4 ∨ (1 - y)*z ≥ 1/4 ∨ (1 - z)*x ≥ 1/4 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  have hA : 0 ≤ x * (1 - x) := mul_nonneg hx.1.le (by linarith)
  have hB : 0 ≤ y * (1 - y) := mul_nonneg hy.1.le (by linarith)
  have hC : 0 ≤ z * (1 - z) := mul_nonneg hz.1.le (by linarith)
  have hA' : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1/2)]
  have hB' : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1/2)]
  have hC' : z * (1 - z) ≤ 1 / 4 := by nlinarith [sq_nonneg (z - 1/2)]
  have hAB : x * (1 - x) * (y * (1 - y)) ≤ 1 / 4 * (1 / 4) := mul_le_mul hA' hB' hB (by norm_num)
  have hABC : x * (1 - x) * (y * (1 - y)) * (z * (1 - z)) ≤ 1 / 4 * (1 / 4) * (1 / 4) :=
    mul_le_mul hAB hC' hC (by norm_num)
  have hP : (x * y * z) ^ 2 = x * (1 - x) * (y * (1 - y)) * (z * (1 - z)) := by
    linear_combination (x * y * z) * hab
  have hpos : 0 < x * y * z := mul_pos (mul_pos hx.1 hy.1) hz.1
  have hPle : x * y * z ≤ 1 / 8 := by nlinarith
  have hsum : (1 - x) * y + (1 - y) * z + (1 - z) * x = 1 - 2 * (x * y * z) := by
    linear_combination hab
  linarith
