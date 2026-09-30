-- Prove2me | solution 1 for lean_workbook_plus_27490
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:49:22.279842+00:00
-- url     : https://prove2.me/submissions/d5f25b42-e5fe-4576-9c14-fda0b2961b2f

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a : Real) : Real.sqrt ((a ^ 2 + 1) / 2) ≥ (a + 1) / 2 := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (a - 1)]

#print axioms solution
