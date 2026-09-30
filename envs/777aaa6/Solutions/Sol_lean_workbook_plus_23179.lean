-- Prove2me | solution 1 for lean_workbook_plus_23179
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:57.374124+00:00
-- url     : https://prove2.me/submissions/176498af-2daf-443e-9067-939147a9970d

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) / (1 + a + b) ≤ a / (1 + a) + b / (1 + b) ∧ a / (1 + a) + b / (1 + b) ≤ (2 * (a + b)) / (2 + a + b)   := by
  have ha1 : 0 < 1 + a := by linarith
  have hb1 : 0 < 1 + b := by linarith
  have hs1 : 0 < 1 + a + b := by linarith
  have hs2 : 0 < 2 + a + b := by linarith
  have hgap1 : a / (1 + a) + b / (1 + b) - (a + b) / (1 + a + b) =
      a * b * (2 + a + b) / ((1 + a) * (1 + b) * (1 + a + b)) := by
    field_simp [ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hs1]
    <;> ring
  have hgap2 : (2 * (a + b)) / (2 + a + b) - (a / (1 + a) + b / (1 + b)) =
      (a - b) ^ 2 / ((1 + a) * (1 + b) * (2 + a + b)) := by
    field_simp [ne_of_gt ha1, ne_of_gt hb1, ne_of_gt hs2]
    <;> ring
  constructor
  · apply sub_nonneg.mp
    rw [hgap1]
    exact div_nonneg (mul_nonneg (mul_nonneg ha hb) (le_of_lt hs2))
      (le_of_lt (mul_pos (mul_pos ha1 hb1) hs1))
  · apply sub_nonneg.mp
    rw [hgap2]
    exact div_nonneg (sq_nonneg (a - b))
      (le_of_lt (mul_pos (mul_pos ha1 hb1) hs2))

#print axioms solution
