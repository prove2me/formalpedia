-- Prove2me | solution 1 for lean_workbook_plus_71130
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:57.026968+00:00
-- url     : https://prove2.me/submissions/ac924625-e163-4d35-b19c-b1facbf0ef1e

import Mathlib

theorem solution (x : ℝ) :
    x^4 + 4*x^3 + 6*x^2 + 4*x + 1 = 0 ↔ x = -1 := by
  have hi : x^4 + 4*x^3 + 6*x^2 + 4*x + 1 = (x + 1)^4 := by ring
  rw [hi]
  constructor
  · intro h
    have hx : x + 1 = 0 := pow_eq_zero h
    linarith
  · intro h
    rw [h]
    norm_num

#print axioms solution
