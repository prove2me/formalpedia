-- Prove2me | solution 1 for lean_workbook_plus_1237
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:11.943238+00:00
-- url     : https://prove2.me/submissions/d7e10fef-59c5-4af0-a531-c4eadf11b8d3

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≤ 1) : 1 / a + 1 / b + a ^ 2 + b ^ 2 + 3 * a + 3 * b ≥ 15 / 2   := by
  have bound : ∀ t : ℝ, 0 < t → (15 : ℝ) / 4 ≤ 1 / t + t ^ 2 + 3 * t := by
    intro t ht
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * t by positivity)).mp
    have he : (1 / t + t ^ 2 + 3 * t) * (4 * t) - (15 / 4) * (4 * t) =
        (2 * t - 1) ^ 2 * (t + 4) := by
      field_simp [ne_of_gt ht]
      ring
    have hp := mul_nonneg (sq_nonneg (2 * t - 1)) (by linarith : 0 ≤ t + 4)
    nlinarith only [he, hp]
  have h1 := bound a ha
  have h2 := bound b hb
  linarith only [h1, h2]

#print axioms solution
