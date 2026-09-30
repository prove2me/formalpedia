-- Prove2me | solution 1 for lean_workbook_plus_11733
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:53.273714+00:00
-- url     : https://prove2.me/submissions/d1d57e27-9376-4744-a1df-603d8a2363a1

import Mathlib
set_option autoImplicit false

theorem solution (F : ℕ → ℕ) (h₁ : F 1 = 1 ∧ F 2 = 1) (h₂ : ∀ n, F (n + 2) = F (n + 1) + F n) : F 8 = 21   := by
  rw [h₂ 6, h₂ 5, h₂ 4, h₂ 3, h₂ 2, h₂ 1]
  simp [h₁]

#print axioms solution
