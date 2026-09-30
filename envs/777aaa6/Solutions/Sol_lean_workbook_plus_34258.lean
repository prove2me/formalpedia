-- Prove2me | solution 1 for lean_workbook_plus_34258
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:59:58.808779+00:00
-- url     : https://prove2.me/submissions/63595439-458a-4faf-983d-dc844939ddc2

import Mathlib

namespace ShiftedFourthPowerSystem

def System (x y : ℝ) : Prop :=
  x ^ 4 - y ^ 4 = 240 ∧
    x ^ 3 - 2 * y ^ 3 = 3 * (x ^ 2 - 4 * y ^ 2) - 4 * (x - 8 * y)

theorem shifted_equality (x y : ℝ) (h : System x y) :
    (x - 2) ^ 4 = (y - 4) ^ 4 := by
  linear_combination h.1 - 8 * h.2

theorem linear_branches (x y : ℝ) (h : System x y) :
    x = y - 2 ∨ x + y = 6 := by
  have h4 := shifted_equality x y h
  have h4' : ((x - 2) ^ 2) ^ 2 = ((y - 4) ^ 2) ^ 2 := by
    convert h4 using 1 <;> ring
  have h2 := (sq_eq_sq₀ (sq_nonneg (x - 2)) (sq_nonneg (y - 4))).mp h4'
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem full_classification (x y : ℝ) : System x y ↔
    (x = 4 ∧ y = 2) ∨ (x = -4 ∧ y = -2) := by
  constructor
  · intro h
    rcases linear_branches x y h with hx | hs
    · have h1 := h.1
      rw [hx] at h1
      have hf : (y + 2) * (y ^ 2 - 5 * y + 14) = 0 := by
        linear_combination -h1 / 8
      have hp : 0 < y ^ 2 - 5 * y + 14 := by nlinarith [sq_nonneg (2 * y - 5)]
      have hy : y = -2 := by
        have := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hp)
        linarith
      exact Or.inr ⟨by linarith, hy⟩
    · have hx : x = 6 - y := by linarith
      have h1 := h.1
      rw [hx] at h1
      have hf : (y - 2) * (y ^ 2 - 7 * y + 22) = 0 := by
        linear_combination -h1 / 24
      have hp : 0 < y ^ 2 - 7 * y + 22 := by nlinarith [sq_nonneg (2 * y - 7)]
      have hy : y = 2 := by
        have := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hp)
        linarith
      exact Or.inl ⟨by linarith, hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num [System]

theorem positive_classification (x y : ℝ) :
    (System x y ∧ 0 < x ∧ 0 < y) ↔ x = 4 ∧ y = 2 := by
  rw [full_classification]
  constructor
  · rintro ⟨h | h, hx, _⟩
    · exact h
    · linarith [h.1]
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem genuine_models : System 4 2 ∧ System (-4) (-2) :=
  ⟨(full_classification _ _).mpr (Or.inl ⟨rfl, rfl⟩),
    (full_classification _ _).mpr (Or.inr ⟨rfl, rfl⟩)⟩

end ShiftedFourthPowerSystem

theorem solution (x y : ℝ) (h1 : x ^ 4 - y ^ 4 = 240)
    (h2 : x ^ 3 - 2 * y ^ 3 = 3 * (x ^ 2 - 4 * y ^ 2) - 4 * (x - 8 * y)) :
    (x - 2) ^ 4 = (y - 4) ^ 4 :=
  ShiftedFourthPowerSystem.shifted_equality x y ⟨h1, h2⟩

#print axioms ShiftedFourthPowerSystem.shifted_equality
#print axioms ShiftedFourthPowerSystem.linear_branches
#print axioms ShiftedFourthPowerSystem.full_classification
#print axioms ShiftedFourthPowerSystem.positive_classification
#print axioms ShiftedFourthPowerSystem.genuine_models
#print axioms solution
