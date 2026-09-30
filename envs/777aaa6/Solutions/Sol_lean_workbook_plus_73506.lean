-- Prove2me | solution 1 for lean_workbook_plus_73506
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:40:57.414679+00:00
-- url     : https://prove2.me/submissions/7d098d53-0e67-43e4-a728-ddd7fb97d323

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + 2 * b + 3 * c) / (4 * a + 5 * b + 6 * c) +
      (2 * a + 3 * b + c) / (5 * a + 6 * b + 4 * c) +
      (3 * a + b + 2 * c) / (6 * a + 4 * b + 5 * c) ≤ 6 / 5 := by
  let d₁ := 4 * a + 5 * b + 6 * c
  let d₂ := 5 * a + 6 * b + 4 * c
  let d₃ := 6 * a + 4 * b + 5 * c
  have hd₁ : 0 < d₁ := by dsimp [d₁]; positivity
  have hd₂ : 0 < d₂ := by dsimp [d₂]; positivity
  have hd₃ : 0 < d₃ := by dsimp [d₃]; positivity
  have hid :
      (6 / 5 - ((a + 2 * b + 3 * c) / d₁ + (2 * a + 3 * b + c) / d₂ +
        (3 * a + b + 2 * c) / d₃)) * (5 * (d₁ * d₂ * d₃)) =
      (d₁ - d₂) ^ 2 * d₃ + (d₂ - d₃) ^ 2 * d₁ + (d₃ - d₁) ^ 2 * d₂ := by
    field_simp [ne_of_gt hd₁, ne_of_gt hd₂, ne_of_gt hd₃]
    dsimp [d₁, d₂, d₃]
    ring
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left (b := 5 * (d₁ * d₂ * d₃))
    (by rw [hid]; positivity) (by positivity)

#print axioms solution
