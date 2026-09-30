-- Prove2me | solution 1 for lean_workbook_plus_64100
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:32.6648+00:00
-- url     : https://prove2.me/submissions/e67afec8-dd63-4986-b975-6412b323a7a7

import Mathlib
set_option autoImplicit false

theorem solution {n:ℤ} : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 → n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1   := by
  rintro (h | h | h) <;> simp [pow_two, Int.mul_emod, h]

#print axioms solution
