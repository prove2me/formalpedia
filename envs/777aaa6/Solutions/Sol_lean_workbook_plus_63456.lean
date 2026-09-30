-- Prove2me | solution 1 for lean_workbook_plus_63456
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:23.769328+00:00
-- url     : https://prove2.me/submissions/17ad2614-1d6d-490a-9dec-d3a2c8525588

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a + b + c = 0) (h₂ : a ^ 3 + b ^ 3 + c ^ 3 = 3 * a * b * c) : (a ^ 5 + b ^ 5 + c ^ 5) / 5 = (a ^ 3 + b ^ 3 + c ^ 3) / 3 * (a ^ 2 + b ^ 2 + c ^ 2) / 2   := by
  have h₃ : c = -(a + b) := by linarith
  rw [h₃] at h₂ ⊢
  ring

#print axioms solution
