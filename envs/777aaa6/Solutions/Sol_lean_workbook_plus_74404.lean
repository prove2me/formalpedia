-- Prove2me | solution 1 for lean_workbook_plus_74404
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:50:12.244637+00:00
-- url     : https://prove2.me/submissions/8997e0ef-9e3b-4cdb-acaa-0e1997b684d2

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) (ha : a ≥ 0) : 5 * (a ^ 2 - a + 1) ^ 2 ≥ 2 * (1 + a ^ 4)   := by
  nlinarith only [sq_nonneg ((a - 1) ^ 2), mul_nonneg ha (sq_nonneg (a - 1)), sq_nonneg a]

#print axioms solution
