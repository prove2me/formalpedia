-- Prove2me | solution 1 for lean_workbook_plus_67435
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:35.868704+00:00
-- url     : https://prove2.me/submissions/df615143-e502-4f18-81ed-6a2c5a81a729

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (y / (x + y) * (1 - y / (x + y)) + z / (y + z) * (1 - z / (y + z)) + x / (z + x) * (1 - x / (z + x))) ≤ 9 / 4   := by
  nlinarith [sq_nonneg (y / (x + y) - 1 / 2),
    sq_nonneg (z / (y + z) - 1 / 2),
    sq_nonneg (x / (z + x) - 1 / 2)]

#print axioms solution
