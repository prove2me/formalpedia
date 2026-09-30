-- Prove2me | solution 1 for lean_workbook_plus_64366
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:27.44699+00:00
-- url     : https://prove2.me/submissions/5f91e4a0-d147-4a21-9a2b-d77914cd1848

import Mathlib
set_option autoImplicit false

theorem solution (a c : ℝ) : 24 * a ^ 2 + 6 * c ^ 2 ≥ 24 * a * c   := by
  nlinarith [sq_nonneg (2 * a - c)]

#print axioms solution
