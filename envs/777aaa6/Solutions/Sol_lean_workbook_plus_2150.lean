-- Prove2me | solution 1 for lean_workbook_plus_2150
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:00:01.249158+00:00
-- url     : https://prove2.me/submissions/bb404a73-517f-4e16-b791-69194d649ed4

import Mathlib
set_option autoImplicit false

theorem solution  (q : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 + 2 * x + q)
  (h₁ : ∃ x, f x = 0) :
  q ≤ 1   := by
  obtain ⟨x, h₂⟩ := h₁
  rw [h₀] at h₂
  have h₃ := sq_nonneg (x + 1)
  nlinarith

#print axioms solution
