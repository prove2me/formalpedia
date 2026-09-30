-- Prove2me | solution 1 for lean_workbook_plus_6334
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:28.26409+00:00
-- url     : https://prove2.me/submissions/ccf1dd78-9de2-49d7-996c-621a5fe122e2

import Mathlib
set_option autoImplicit false

theorem solution (b : ℕ) (h₁ : ∃ k : ℕ, k^2 = (b + 1)) : ∃ l : ℕ, l^2 = 4 * (b + 1)   := by
  obtain ⟨k, hk⟩ := h₁
  use 2 * k
  rw [mul_pow, hk]
  ring

#print axioms solution
