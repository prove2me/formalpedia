-- Prove2me | solution 1 for lean_workbook_plus_66532
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:40.79948+00:00
-- url     : https://prove2.me/submissions/83c9c950-99c5-4922-b92c-d5fffe7b9033

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (hx: (x - 1) * (x - 3) ≥ 0) :
  x ≤ 1 ∨ x ≥ 3 := by
  by_cases h : x ≤ 1
  · exact Or.inl h
  · right
    have hx1 : 1 < x := lt_of_not_ge h
    nlinarith [hx, hx1]

#print axioms solution
