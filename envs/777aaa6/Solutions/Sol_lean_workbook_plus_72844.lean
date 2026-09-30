-- Prove2me | solution 1 for lean_workbook_plus_72844
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:23.853184+00:00
-- url     : https://prove2.me/submissions/4780304b-e2e8-4165-964d-08f730939aba

import Mathlib
set_option autoImplicit false

theorem solution (a b n : ℝ) (ha : 1 < a) (hb : 1 < b) (hn : 1 < n) :
    (1 / (a + n) ^ 2 + 1 / (b + n) ^ 2) ≥ 1 / (a * b + n ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hn0 : 0 < n := by linarith
  have hd : 0 < (a + n) ^ 2 * (b + n) ^ 2 * (a * b + n ^ 2) := by positivity
  apply (mul_le_mul_iff_left₀ hd).mp
  have han : a + n ≠ 0 := by positivity
  have hbn : b + n ≠ 0 := by positivity
  have hab : a * b + n ^ 2 ≠ 0 := by positivity
  field_simp
  nlinarith [mul_nonneg (mul_nonneg ha0.le hb0.le) (sq_nonneg (a - b)),
    sq_nonneg (a * b - n ^ 2)]

#print axioms solution
