-- Prove2me | solution 1 for lean_workbook_plus_47335
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:35.229673+00:00
-- url     : https://prove2.me/submissions/c844cb06-3004-4abf-87e1-dcfdc0a26303

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : 4 * x - x ^ 4 ≤ 3   := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1)]

#print axioms solution
