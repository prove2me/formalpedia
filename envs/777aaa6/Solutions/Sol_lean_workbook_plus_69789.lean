-- Prove2me | solution 1 for lean_workbook_plus_69789
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:33.153682+00:00
-- url     : https://prove2.me/submissions/b728266a-5c7e-41d6-bd24-b631a7a0b64d

import Mathlib
set_option autoImplicit false

theorem solution (b c : ℝ) : (b + c) ^ 2 * (b - c) ^ 2 * (4 * b ^ 2 - b * c + 4 * c ^ 2) ≥ 0   := by
  apply mul_nonneg
  apply mul_nonneg <;> apply sq_nonneg
  nlinarith [sq_nonneg (b - c), sq_nonneg b, sq_nonneg c]

#print axioms solution
