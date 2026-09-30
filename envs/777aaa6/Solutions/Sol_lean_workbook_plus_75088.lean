-- Prove2me | solution 1 for lean_workbook_plus_75088
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:27:49.702723+00:00
-- url     : https://prove2.me/submissions/9c57f1d5-8a2c-4aaf-9c31-cb97e3f5c97f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (z : ℂ) :
    (z ^ 2 + (2 * Complex.I - 3) * z + (5 - Complex.I) = 0) ↔
      (z = 1 + Complex.I ∨ z = 2 - 3 * Complex.I) := by
  have hf : z ^ 2 + (2 * Complex.I - 3) * z + (5 - Complex.I) =
      (z - (1 + Complex.I)) * (z - (2 - 3 * Complex.I)) := by
    linear_combination 3 * Complex.I_sq
  rw [hf]
  simp only [mul_eq_zero, sub_eq_zero]

#print axioms solution
