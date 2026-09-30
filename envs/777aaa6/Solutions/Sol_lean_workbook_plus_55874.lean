-- Prove2me | solution 1 for lean_workbook_plus_55874
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:47.462499+00:00
-- url     : https://prove2.me/submissions/1a0ea0ad-9984-49a5-9afd-901d1d6ac756

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (x + y + z) / 3 ≤ Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3)   := by
  apply Real.le_sqrt_of_sq_le
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

#print axioms solution
