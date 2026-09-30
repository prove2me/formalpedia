-- Prove2me | solution 1 for lean_workbook_plus_11382
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:59.936742+00:00
-- url     : https://prove2.me/submissions/b7d474c8-5983-414a-993d-4c6502276a9e

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≥ (x + y) / 2   := by
  have h2 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  apply Real.le_sqrt_of_sq_le
  nlinarith

#print axioms solution
