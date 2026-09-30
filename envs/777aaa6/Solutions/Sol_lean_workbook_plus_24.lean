-- Prove2me | solution 1 for lean_workbook_plus_24
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:25.098804+00:00
-- url     : https://prove2.me/submissions/82519cde-9e31-4b6c-8a12-3e4a7c0edd96

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c ≥ 2 * (1 / (b + c) + 1 / (c + a) + 1 / (a + b))   := by
  have pair : ∀ u v : ℝ, 0 < u → 0 < v → 4 / (u + v) ≤ 1 / u + 1 / v := by
    intro u v hu hv
    apply (div_le_iff₀ (add_pos hu hv)).mpr
    apply (mul_le_mul_iff_right₀ (mul_pos hu hv)).mp
    have he : ((1 / u + 1 / v) * (u + v) - 4) * (u * v) = (u - v) ^ 2 := by
      field_simp [ne_of_gt hu, ne_of_gt hv]
      ring
    nlinarith only [he, sq_nonneg (u - v)]
  have h1 := pair b c hb hc
  have h2 := pair c a hc ha
  have h3 := pair a b ha hb
  simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
  linarith only [h1, h2, h3]

#print axioms solution
