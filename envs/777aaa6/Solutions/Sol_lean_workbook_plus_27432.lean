-- Prove2me | solution 1 for lean_workbook_plus_27432
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:55:53.112586+00:00
-- url     : https://prove2.me/submissions/c828d799-6c44-43d7-9274-ce8f79627ac6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (m : Real) :
    m ^ 3 - 6 * m ^ 2 + 11 * m - 6 = 0 ↔ m = 1 ∨ m = 2 ∨ m = 3 := by
  have hf : m ^ 3 - 6 * m ^ 2 + 11 * m - 6 = (m - 1) * ((m - 2) * (m - 3)) := by
    ring
  rw [hf]
  simp only [mul_eq_zero, sub_eq_zero]

#print axioms solution
