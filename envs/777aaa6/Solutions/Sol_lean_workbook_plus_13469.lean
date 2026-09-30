-- Prove2me | solution 1 for lean_workbook_plus_13469
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:36.13555+00:00
-- url     : https://prove2.me/submissions/4bcef2cf-cafa-429f-a3fb-5e59f637ab79

import Mathlib
set_option autoImplicit false

theorem solution  (f₀ f₁ f₂ f₃ : ℚ)
  (h₀ : f₀ = (f₁ + f₂) / 2)
  (h₁ : f₁ = (1 + f₂) / 2)
  (h₂ : f₂ = (f₁ + f₃) / 2)
  (h₃ : f₃ = (f₁ + 0) / 2) :
  f₀ = 7 / 10   := by
  revert h₀ h₁ h₂ h₃
  intros h₀ h₁ h₂ h₃
  field_simp at *
  linarith

#print axioms solution
