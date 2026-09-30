-- Prove2me | solution 1 for lean_workbook_plus_47673
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:26.238655+00:00
-- url     : https://prove2.me/submissions/f643b218-4279-4c99-ae78-06c1213a2e3b

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℕ) (hab : Nat.Coprime a b) (n : ℕ) : Nat.Coprime a (b^n)   := by
  exact Nat.Coprime.pow_right n hab

#print axioms solution
