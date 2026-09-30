-- Prove2me | solution 1 for lean_workbook_plus_71593
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:16.980189+00:00
-- url     : https://prove2.me/submissions/74d24b42-cf45-4dba-aba7-1dd057852bbc

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : |x| = if x < 0 then -x else x := by
  split_ifs with h
  · exact abs_of_neg h
  · exact abs_of_nonneg (le_of_not_gt h)

#print axioms solution
