-- Prove2me | solution 1 for lean_workbook_plus_29115
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:42:10.676874+00:00
-- url     : https://prove2.me/submissions/738f3211-745a-4cfb-b8ec-47e916ef5312

import Mathlib
set_option autoImplicit false

theorem solution  (f g : ℝ → ℝ)
  (h₀ : ∀ x, 0 ≤ x ∧ x ≤ 1 → f x = x)
  (h₁ : ∀ x, 1 < x ∧ x ≤ 2 → f x = x - 2)
  (h₂ : ∀ x, 0 ≤ x ∧ x ≤ 1 → g x = -x)
  (h₃ : ∀ x, 1 < x ∧ x ≤ 2 → g x = -x + 2) :
  ∀ x, 0 ≤ x ∧ x ≤ 2 → f x + g x = 0   := by
  rintro x ⟨hx₁, hx₂⟩
  cases' le_or_gt x 1 with hle hlt
  rw [h₀ x ⟨hx₁, hle⟩, h₂ x ⟨hx₁, hle⟩]
  linarith
  rw [h₁ x ⟨hlt, hx₂⟩, h₃ x ⟨hlt, hx₂⟩]
  linarith

#print axioms solution
