-- Prove2me | solution 1 for lean_workbook_plus_71695
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:22.557632+00:00
-- url     : https://prove2.me/submissions/d7aa9a3f-b755-4bc9-bb81-8e27f5750b85

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) (h : x^2 + 2 * x + 3 / 4 = 0) :
    x = -3 / 2 ∨ x = -1 / 2 := by
  have hz : (x + 3 / 2) * (x + 1 / 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · left; linarith
  · right; linarith

#print axioms solution
