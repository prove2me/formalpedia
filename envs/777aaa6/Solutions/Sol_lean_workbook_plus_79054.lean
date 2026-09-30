-- Prove2me | solution 1 for lean_workbook_plus_79054
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:09.020924+00:00
-- url     : https://prove2.me/submissions/982358a9-cbb1-4519-a418-e63f1500d9a8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℤ)
    (h₀ : 0 < a ∧ 0 < b)
    (h₁ : ∀ k : ℕ, (2 * k * b) ≤ (2 * k + 1) * a)
    (h₂ : ∀ j : ℕ, (2 * j + 1) * a ≤ (2 * j + 2) * b) : a = b := by
  have h1 := h₁ a.toNat
  have h2 := h₂ b.toNat
  rw [Int.toNat_of_nonneg (le_of_lt h₀.1)] at h1
  rw [Int.toNat_of_nonneg (le_of_lt h₀.2)] at h2
  apply le_antisymm
  · by_contra hn
    have hgap : b + 1 ≤ a := by omega
    nlinarith [mul_nonneg (by omega : 0 ≤ 2 * b + 1) (by omega : 0 ≤ a - b - 1)]
  · by_contra hn
    have hgap : a + 1 ≤ b := by omega
    nlinarith [mul_nonneg (by omega : 0 ≤ a) (by omega : 0 ≤ b - a - 1)]

#print axioms solution
