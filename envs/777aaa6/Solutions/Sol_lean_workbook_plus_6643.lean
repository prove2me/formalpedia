-- Prove2me | solution 1 for lean_workbook_plus_6643
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:54:24.326962+00:00
-- url     : https://prove2.me/submissions/19d75bae-84ee-42dd-9585-83d1d198fc57

import Mathlib
set_option autoImplicit false

theorem solution (a b x : ℕ) (hab : Nat.Coprime a b) (h : x ≡ 0 [ZMOD a * b]) : x ≡ 0 [ZMOD a] ∧ x ≡ 0 [ZMOD b]   := by
  exact ⟨h.of_mul_right _, h.of_mul_left _⟩

#print axioms solution
