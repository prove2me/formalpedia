-- Prove2me | solution 1 for lean_workbook_plus_73240
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:41:07.569429+00:00
-- url     : https://prove2.me/submissions/0bfb9ef5-616e-47b3-8cc0-dec291d459e3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem reciprocal_rewrite (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    1 / (1 + x + y⁻¹) = y / (x * y + y + 1) := by
  have hd₁ : 0 < 1 + x + y⁻¹ := by positivity
  have hd₂ : 0 < x * y + y + 1 := by positivity
  apply (div_eq_div_iff (ne_of_gt hd₁) (ne_of_gt hd₂)).mpr
  field_simp [ne_of_gt hy]
  <;> ring

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (1 + a + b⁻¹) + 1 / (1 + b + c⁻¹) + 1 / (1 + c + a⁻¹) ≤ 1 := by
  rw [reciprocal_rewrite a b ha hb, reciprocal_rewrite b c hb hc,
    reciprocal_rewrite c a hc ha]
  have hd₁ : 0 < a * b + b + 1 := by positivity
  have hd₂ : 0 < b * c + c + 1 := by positivity
  have hd₃ : 0 < c * a + a + 1 := by positivity
  have hid :
      (1 - (b / (a * b + b + 1) + c / (b * c + c + 1) + a / (c * a + a + 1))) *
        ((a * b + b + 1) * (b * c + c + 1) * (c * a + a + 1)) =
      (a * b * c - 1) ^ 2 := by
    field_simp [ne_of_gt hd₁, ne_of_gt hd₂, ne_of_gt hd₃]
    <;> ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left
    (b := (a * b + b + 1) * (b * c + c + 1) * (c * a + a + 1))
    (by rw [hid]; exact sq_nonneg _) (by positivity)

#print axioms solution
