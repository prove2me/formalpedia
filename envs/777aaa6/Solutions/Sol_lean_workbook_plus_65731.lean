-- Prove2me | solution 1 for lean_workbook_plus_65731
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:50.773726+00:00
-- url     : https://prove2.me/submissions/37f0e192-daaa-417b-8100-3cd21eb716ff

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ a b : ℝ,
    a > 0 ∧ b > 0 ∧ a ^ 3 / b + 2 * b / a = 3 →
    a ^ 2 + a * b + b ^ 2 ≤ 3 := by
  rintro a b ⟨ha, hb, h⟩
  let t := b / a
  have ht : 0 < t := div_pos hb ha
  have hbt : b = a * t := by dsimp [t]; field_simp
  have heq : a ^ 2 + 2 * t ^ 2 = 3 * t := by
    dsimp [t]
    field_simp [ne_of_gt ha, ne_of_gt hb] at h ⊢
    nlinarith [h]
  have hgap : 3 - (a ^ 2 + a * b + b ^ 2) =
      (t - 1) ^ 2 * (2 * t ^ 2 + 3 * t + 3) := by
    rw [hbt]
    linear_combination -(1 + t + t ^ 2) * heq
  have hp : 0 ≤ (t - 1) ^ 2 * (2 * t ^ 2 + 3 * t + 3) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  linarith

theorem sharp : ((1 : ℝ) ^ (3 : ℕ)) / 1 + (2 : ℝ) * 1 / 1 = 3 ∧
    ((1 : ℝ) ^ (2 : ℕ)) + 1 * 1 + 1 ^ (2 : ℕ) = 3 := by
  constructor <;> simp only [one_pow, div_one, mul_one] <;> norm_num

#print axioms solution
#print axioms sharp
