-- Prove2me | solution 1 for lean_workbook_plus_2076
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:27.930274+00:00
-- url     : https://prove2.me/submissions/4f162fe0-f439-460c-9c8b-25391b663ab2

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (hab: a ∈ Set.Icc 1 2 ∧ b ∈ Set.Icc 1 2): 4/3 ≤ (a+1)/(b+2) + (b+1)/(a+2) ∧ (a+1)/(b+2) + (b+1)/(a+2) ≤ 3/2   := by
  rcases hab with ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩
  have ha : 0 < a + 2 := by linarith
  have hb : 0 < b + 2 := by linarith
  have hd : 0 < (a + 2) * (b + 2) := mul_pos ha hb
  have he : ((a + 1) / (b + 2) + (b + 1) / (a + 2)) * ((a + 2) * (b + 2)) =
      (a + 1) * (a + 2) + (b + 1) * (b + 2) := by
    field_simp [ne_of_gt ha, ne_of_gt hb]
  have hab1 : 1 ≤ a * b := by nlinarith [mul_nonneg (by linarith : 0 ≤ a - 1) (by linarith : 0 ≤ b - 1)]
  constructor
  · apply (mul_le_mul_iff_right₀ hd).mp
    nlinarith only [he, sq_nonneg (a - b), hab1, ha1, hb1]
  · apply (mul_le_mul_iff_right₀ hd).mp
    have h1 := mul_nonneg (by linarith : 0 ≤ a - 1) (by linarith : 0 ≤ 2 - a)
    have h2 := mul_nonneg (by linarith : 0 ≤ b - 1) (by linarith : 0 ≤ 2 - b)
    have h3 := mul_nonneg (by linarith : 0 ≤ 2 - a) (by linarith : 0 ≤ 2 - b)
    nlinarith only [he, h1, h2, h3]

#print axioms solution
