-- Prove2me | solution 1 for lean_workbook_plus_64014
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:35.713948+00:00
-- url     : https://prove2.me/submissions/4eac0334-d9d1-4980-9fa8-4bc32a29a000

import Mathlib
set_option autoImplicit false

theorem solution  (x y z : ℝ) :
  (x + y + z)^2 ≤ (x^2 + y^2 + 1) * (1 + 1 + z^2)   := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1)]

#print axioms solution
