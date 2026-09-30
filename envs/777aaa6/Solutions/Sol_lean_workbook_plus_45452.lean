-- Prove2me | solution 1 for lean_workbook_plus_45452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:37.568145+00:00
-- url     : https://prove2.me/submissions/c053c2b1-3470-4510-ba4a-d57405aa0505

import Mathlib
set_option autoImplicit false

theorem solution (k₁ k₂ a b : ℝ) (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (ha : 0 < a) (hb : 0 < b) : k₁ * k₂ * a ^ 3 + (k₁ ^ 2 + k₂ ^ 2 + k₁ * k₂) * (a ^ 2 * b + a * b ^ 2) + k₁ * k₂ * b ^ 3 ≤ (k₁ + k₂) ^ 2 * (a + b) ^ 3 / 4   := by
  have h : 0 ≤ (k₁ - k₂) ^ 2 * (a - b) ^ 2 * (a + b) :=
    mul_nonneg (mul_nonneg (sq_nonneg (k₁ - k₂)) (sq_nonneg (a - b)))
      (le_of_lt (add_pos ha hb))
  nlinarith only [h]

#print axioms solution
