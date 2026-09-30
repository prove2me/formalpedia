-- Prove2me | solution 1 for lean_workbook_plus_24316
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:22.139427+00:00
-- url     : https://prove2.me/submissions/5459152a-48ad-4435-a40f-3e7eea58d08c

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 + 2 * a / (b + c)) * (1 + 2 * b / (c + a)) * (1 + 2 * c / (a + b)) ≥ 2 := by
  have hx : 2 * a / (b + c) ≥ 2 * a / (a + b + c) := by
    apply div_le_div_of_nonneg_left <;> [positivity; positivity; linarith]
  have hy : 2 * b / (c + a) ≥ 2 * b / (a + b + c) := by
    apply div_le_div_of_nonneg_left <;> [positivity; positivity; linarith]
  have hz : 2 * c / (a + b) ≥ 2 * c / (a + b + c) := by
    apply div_le_div_of_nonneg_left <;> [positivity; positivity; linarith]
  have hsum : 2 * a / (a + b + c) + 2 * b / (a + b + c) + 2 * c / (a + b + c) = 2 := by
    field_simp
  have hx0 : 0 ≤ 2 * a / (b + c) := by positivity
  have hy0 : 0 ≤ 2 * b / (c + a) := by positivity
  have hz0 : 0 ≤ 2 * c / (a + b) := by positivity
  nlinarith [mul_nonneg hx0 hy0, mul_nonneg hy0 hz0, mul_nonneg hx0 hz0, mul_nonneg (mul_nonneg hx0 hy0) hz0]
