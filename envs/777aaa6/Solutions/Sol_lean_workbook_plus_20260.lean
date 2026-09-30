-- Prove2me | solution 1 for lean_workbook_plus_20260
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:14.321795+00:00
-- url     : https://prove2.me/submissions/3169322d-5f05-4073-a7d6-d8fafa9a0418

import Mathlib
set_option autoImplicit false

theorem solution (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) : x * y + y * z + z * t + t * x ≤ 1 / 4 * (x + y + z + t) ^ 2   := by
  nlinarith [sq_nonneg (x - y + z - t)]

#print axioms solution
