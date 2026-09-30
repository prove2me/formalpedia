-- Prove2me | solution 1 for lean_workbook_plus_76881
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:15:39.273686+00:00
-- url     : https://prove2.me/submissions/6f52b763-8073-426a-ba68-ca39cdf90a10

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) : |b - a| = |a - b|   := by
  exact abs_sub_comm b a

#print axioms solution
