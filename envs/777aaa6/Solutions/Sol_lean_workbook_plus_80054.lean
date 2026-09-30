-- Prove2me | solution 1 for lean_workbook_plus_80054
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:02.675765+00:00
-- url     : https://prove2.me/submissions/04281938-41a2-43af-8051-6fe457121624

import Mathlib
set_option autoImplicit false

theorem solution (u v : ℝ) (h : u + 2*v > 4) : u^2 + 4*v^2 > 8 := by
  nlinarith [sq_nonneg (u-2*v), sq_nonneg (u+2*v-4)]

#print axioms solution
