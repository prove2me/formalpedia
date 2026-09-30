-- Prove2me | solution 1 for lean_workbook_plus_9007
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:48:16.304292+00:00
-- url     : https://prove2.me/submissions/0abcfb3c-f53a-488e-b12a-e09a1d39614d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem integer_root_quartic_factorization (z : ℂ) :
    z ^ 4 - 12 * z ^ 3 + 49 * z ^ 2 - 78 * z + 40 =
      (z - 1) * (z - 2) * (z - 4) * (z - 5) := by
  ring

theorem solution (x : ℂ) :
    x ^ 4 - 12 * x ^ 3 + 49 * x ^ 2 - 78 * x + 40 = 0 ↔
      x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 5 := by
  rw [integer_root_quartic_factorization]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

#print axioms integer_root_quartic_factorization
#print axioms solution
