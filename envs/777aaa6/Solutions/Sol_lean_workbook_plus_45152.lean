-- Prove2me | solution 1 for lean_workbook_plus_45152
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:10:14.057442+00:00
-- url     : https://prove2.me/submissions/0acf062d-5d20-43d5-a8f9-f1d0d13b5c2c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

theorem cubic_doubling_coefficients (a b c d : ℝ)
    (h₁ : a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d = 1)
    (h₂ : a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d = 2)
    (h₃ : a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 4)
    (h₄ : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 8) :
    a = 1 / 6 ∧ b = 0 ∧ c = 5 / 6 ∧ d = 1 := by
  have ha : a = 1 / 6 := by
    linear_combination (-h₁ + 3 * h₂ - 3 * h₃ + h₄) / 6
  have hb : b = 0 := by
    linear_combination (2 * h₁ - 5 * h₂ + 4 * h₃ - h₄) / 2
  have hc : c = 5 / 6 := by
    linear_combination (-11 * h₁ + 18 * h₂ - 9 * h₃ + 2 * h₄) / 6
  have hd : d = 1 := by
    linear_combination h₁
  exact ⟨ha, hb, hc, hd⟩

theorem cubic_doubling_model :
    (1 / 6 : ℝ) * 0 ^ 3 + (5 / 6) * 0 + 1 = 1 ∧
    (1 / 6 : ℝ) * 1 ^ 3 + (5 / 6) * 1 + 1 = 2 ∧
    (1 / 6 : ℝ) * 2 ^ 3 + (5 / 6) * 2 + 1 = 4 ∧
    (1 / 6 : ℝ) * 3 ^ 3 + (5 / 6) * 3 + 1 = 8 := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem solution (a b c d : ℝ)
    (h₁ : a * 0 ^ 3 + b * 0 ^ 2 + c * 0 + d = 1)
    (h₂ : a * 1 ^ 3 + b * 1 ^ 2 + c * 1 + d = 2)
    (h₃ : a * 2 ^ 3 + b * 2 ^ 2 + c * 2 + d = 4)
    (h₄ : a * 3 ^ 3 + b * 3 ^ 2 + c * 3 + d = 8) :
    a * 4 ^ 3 + b * 4 ^ 2 + c * 4 + d = 15 := by
  rcases cubic_doubling_coefficients a b c d h₁ h₂ h₃ h₄ with ⟨rfl, rfl, rfl, rfl⟩
  ring

#print axioms solution
#print axioms cubic_doubling_coefficients
