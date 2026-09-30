-- Prove2me | solution 1 for lean_workbook_plus_25035
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:49.06029+00:00
-- url     : https://prove2.me/submissions/82b3c952-5a99-4892-8b5f-ab9aff3f5271

import Mathlib
set_option autoImplicit false

theorem solution (A : ℕ) (hA : A ≡ 1 [ZMOD 16]) : ∃ k : ℕ, A = 16 * k + 1   := by
  rw [Int.ModEq] at hA
  use A / 16
  omega

#print axioms solution
