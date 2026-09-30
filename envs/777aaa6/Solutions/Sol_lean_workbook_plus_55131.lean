-- Prove2me | solution 1 for lean_workbook_plus_55131
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:50.72335+00:00
-- url     : https://prove2.me/submissions/d8812cc6-e0ed-4db8-bd0e-e390b98af13a

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (h : a / b = 1) : a = b   := by
  contrapose! h
  apply div_ne_one_of_ne h

#print axioms solution
