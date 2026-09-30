-- Prove2me | solution 1 for lean_workbook_plus_66419
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:13.715298+00:00
-- url     : https://prove2.me/submissions/2f5e2c69-769f-4095-b65f-04b2b65b52de

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : (a + 1 / b) * (b + 1 / a) ≥ 25 / 4   := by
  have ht : a * b ≤ 1 / 4 := by
    nlinarith [sq_nonneg (a - b),
      mul_nonneg (sub_nonneg.mpr hab) (by linarith : (0 : ℝ) ≤ 1 + (a + b))]
  have hg : 0 ≤ (1 / 4 - a * b) * (4 - a * b) :=
    mul_nonneg (by linarith) (by linarith)
  have he : a * b * ((a + 1 / b) * (b + 1 / a)) = (a * b + 1) ^ 2 := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
    <;> ring
  apply (mul_le_mul_iff_right₀ (mul_pos ha hb)).mp
  rw [he]
  nlinarith [hg]

#print axioms solution
