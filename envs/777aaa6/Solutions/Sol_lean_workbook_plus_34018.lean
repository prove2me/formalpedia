-- Prove2me | solution 1 for lean_workbook_plus_34018
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:57.191186+00:00
-- url     : https://prove2.me/submissions/76586f61-f637-4bb4-b65a-2d6d43a2d32a

import Mathlib
set_option autoImplicit false

theorem solution {a b c n : ℤ} (h₁ : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n]   := by
  exact h₁.add_right c

#print axioms solution
