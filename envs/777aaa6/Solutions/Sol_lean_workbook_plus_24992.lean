-- Prove2me | solution 1 for lean_workbook_plus_24992
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:44:49.882367+00:00
-- url     : https://prove2.me/submissions/2af0611a-dfaa-4b56-a3ef-98dc214f9617

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) : 9 * x ^ 2 * y ^ 2 + 4 * x ^ 2 + 54 * x * y ^ 2 + 24 * x + 81 * y ^ 2 + 36 ≥ 12 * x ^ 2 * y + 72 * x * y + 108 * y   := by
  nlinarith [sq_nonneg ((x + 3) * (3 * y - 2))]

#print axioms solution
