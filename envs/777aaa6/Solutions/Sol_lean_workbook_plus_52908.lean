-- Prove2me | solution 1 for lean_workbook_plus_52908
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:42.033909+00:00
-- url     : https://prove2.me/submissions/ddc5de03-060a-4f51-9670-ef318638088f

import Mathlib
set_option autoImplicit false

theorem solution (a : ℝ) : 3 * a * (a + 4) ≤ (3 * a + a + 4) ^ 2 / 4   := by
  have h2 : 0 ≤ (a - 2) ^ 2 := sq_nonneg (a - 2)
  nlinarith [h2]

#print axioms solution
