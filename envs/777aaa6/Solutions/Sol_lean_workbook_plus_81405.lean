-- Prove2me | solution 1 for lean_workbook_plus_81405
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:25.643301+00:00
-- url     : https://prove2.me/submissions/546e8782-a0f7-4b15-b787-071c898136fe

import Mathlib

theorem solution (x : ℕ → ℝ) (n : ℕ) (h₀ : 0 < n)
    (h₁ : ∀ i, 0 ≤ x i) (h₂ : ∀ i, x i^2 ≤ x n^2) :
    ∀ i, -|x n| ≤ x i ∧ x i ≤ |x n| := by
  rw [abs_of_nonneg (h₁ n)]
  intro i
  constructor
  · linarith [h₁ i, h₁ n]
  · exact (sq_le_sq₀ (h₁ i) (h₁ n)).mp (h₂ i)
