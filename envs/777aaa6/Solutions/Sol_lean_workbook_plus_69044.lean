-- Prove2me | solution 1 for lean_workbook_plus_69044
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:00:12.424759+00:00
-- url     : https://prove2.me/submissions/9978f842-a811-40a6-95f2-b464e03b21d3

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = 30 / 4.5) : ⌊x⌋ = 6 := by
  subst x
  norm_num

#print axioms solution
