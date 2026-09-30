-- Prove2me | solution 1 for lean_workbook_plus_20462
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:09.631385+00:00
-- url     : https://prove2.me/submissions/401c502c-709b-4aba-b40e-bc0e5878f74d

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b - 1 / (a * b) ≥ a - 1 / a + b - 1 / b   := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab : 1 ≤ a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  have hp : 0 ≤ (a - 1) * (b - 1) * (a * b - 1) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)) (sub_nonneg.mpr hab)
  have he : a * b * (a * b - 1 / (a * b) - (a - 1 / a + b - 1 / b)) =
      (a - 1) * (b - 1) * (a * b - 1) := by
    field_simp [ne_of_gt ha0, ne_of_gt hb0]
    <;> ring
  apply (mul_le_mul_iff_right₀ (mul_pos ha0 hb0)).mp
  nlinarith only [he, hp]

#print axioms solution
