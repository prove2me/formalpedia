-- Prove2me | solution 1 for lean_workbook_plus_73732
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:50:13.510525+00:00
-- url     : https://prove2.me/submissions/517b1737-b916-40cf-9d0b-22ac7097f018

import Mathlib
set_option autoImplicit false

theorem solution (x y : ℝ) : |x + y| = |x| + |y| ↔ x*y ≥ 0   := by
  exact (abs_add_eq_add_abs_iff x y).trans mul_nonneg_iff.symm

#print axioms solution
