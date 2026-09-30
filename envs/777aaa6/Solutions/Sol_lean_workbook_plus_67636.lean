-- Prove2me | solution 1 for lean_workbook_plus_67636
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:27.160727+00:00
-- url     : https://prove2.me/submissions/cfe52648-d963-425f-9a28-e74cf6f4852d

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) :
  (x / (x + y)) ^ 2 + (y / (z + x)) ^ 2 + (z / (y + z)) ^ 2 ≥
    1 / 3 * (x / (x + y) + y / (z + x) + z / (y + z)) ^ 2   := by
  have := sq_nonneg (x / (x + y) - y / (z + x))
  have := sq_nonneg (y / (z + x) - z / (y + z))
  have := sq_nonneg (z / (y + z) - x / (x + y))
  linarith

#print axioms solution
