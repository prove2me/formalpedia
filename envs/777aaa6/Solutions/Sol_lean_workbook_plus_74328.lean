-- Prove2me | solution 1 for lean_workbook_plus_74328
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:06:01.996261+00:00
-- url     : https://prove2.me/submissions/aa102d78-c3fb-4407-85c9-5e14d77fdf80

import Mathlib
set_option autoImplicit false

theorem solution {f : ℕ → ℕ} (h : f 1 = f 1 ^ 2) : f 1 = 0 ∨ f 1 = 1   := by
  by_cases h0 : f 1 = 0
  · exact Or.inl h0
  right
  by_contra h1
  have h2 : 2 ≤ f 1 := by omega
  have hm : 2 * f 1 ≤ f 1 * f 1 := Nat.mul_le_mul_right (f 1) h2
  nlinarith

#print axioms solution
