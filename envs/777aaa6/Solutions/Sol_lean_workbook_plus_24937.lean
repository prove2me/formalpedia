-- Prove2me | solution 1 for lean_workbook_plus_24937
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:50.784869+00:00
-- url     : https://prove2.me/submissions/790116d2-a636-4cd3-81c4-d756b5067a32

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) : 4 * x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 + 1 ≥ 6 * x * y   := by
  have h1 := sq_nonneg (2 * x * y - 1)
  have h2 := sq_nonneg (x - y)
  nlinarith

#print axioms solution
