-- Prove2me | solution 1 for lean_workbook_plus_70353
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:55:27.135075+00:00
-- url     : https://prove2.me/submissions/2597a66c-6611-4bc5-a63e-03766a8f398e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem solution (a b c : ℝ) (h₁ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₂ : a ≤ b ∧ b ≤ c) : a / b + b / c + c / a ≥ b / a + c / b + a / c := by
  have hid : a/b + b/c + c/a - (b/a + c/b + a/c) =
      (b-a)*(c-b)*(c-a)/(a*b*c) := by
    field_simp [ne_of_gt h₁.1, ne_of_gt h₁.2.1, ne_of_gt h₁.2.2]
    <;> ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr h₂.1) (sub_nonneg.mpr h₂.2))
      (sub_nonneg.mpr (h₂.1.trans h₂.2)))
    (le_of_lt (mul_pos (mul_pos h₁.1 h₁.2.1) h₁.2.2))
