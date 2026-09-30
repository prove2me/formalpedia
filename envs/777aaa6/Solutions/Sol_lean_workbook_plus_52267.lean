-- Prove2me | solution 1 for lean_workbook_plus_52267
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:34:34.176381+00:00
-- url     : https://prove2.me/submissions/48930305-4139-4306-86d5-545c41b0b36e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

def cyclotomicSignProduct (x : ℝ) : ℝ := x * (1 - x) * (x ^ 2 + x + 1) * (x ^ 2 - x + 1)

private theorem quadratic_cofactors_positive (x : ℝ) :
    0 < x ^ 2 + x + 1 ∧ 0 < x ^ 2 - x + 1 := by
  constructor
  · nlinarith [sq_nonneg (x + 1 / 2)]
  · nlinarith [sq_nonneg (x - 1 / 2)]

theorem cyclotomic_product_positive_iff (x : ℝ) :
    0 < cyclotomicSignProduct x ↔ 0 < x ∧ x < 1 := by
  obtain ⟨hp, hm⟩ := quadratic_cofactors_positive x
  unfold cyclotomicSignProduct
  rw [mul_pos_iff_of_pos_right hm, mul_pos_iff_of_pos_right hp]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨hx, by linarith⟩
    · linarith
  · rintro ⟨hx, hy⟩
    exact mul_pos hx (by linarith)

theorem cyclotomic_product_nonnegative_iff (x : ℝ) :
    0 ≤ cyclotomicSignProduct x ↔ 0 ≤ x ∧ x ≤ 1 := by
  obtain ⟨hp, hm⟩ := quadratic_cofactors_positive x
  unfold cyclotomicSignProduct
  rw [mul_nonneg_iff_of_pos_right hm, mul_nonneg_iff_of_pos_right hp]
  constructor
  · intro h
    rcases mul_nonneg_iff.mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨hx, by linarith⟩
    · linarith
  · rintro ⟨hx, hy⟩
    exact mul_nonneg hx (by linarith)

theorem cyclotomic_product_zero_iff (x : ℝ) :
    cyclotomicSignProduct x = 0 ↔ x = 0 ∨ x = 1 := by
  obtain ⟨hp, hm⟩ := quadratic_cofactors_positive x
  unfold cyclotomicSignProduct
  simp only [mul_eq_zero, hp.ne', hm.ne', or_false]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem solution : ¬ (∀ x : ℝ, x * (1 - x) * (x ^ 2 + x + 1) * (x ^ 2 - x + 1) > 0) := by
  intro h
  have := h 0
  norm_num at this

#print axioms solution
#print axioms cyclotomic_product_positive_iff
#print axioms cyclotomic_product_nonnegative_iff
#print axioms cyclotomic_product_zero_iff
