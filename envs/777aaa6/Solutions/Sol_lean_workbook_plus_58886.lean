-- Prove2me | solution 1 for lean_workbook_plus_58886
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:54.723981+00:00
-- url     : https://prove2.me/submissions/0ff03599-d4c5-4b69-95ae-e8af99cb0379

import Mathlib

theorem solution (a b : ℝ) (h₁ : a > b) (h₂ : b > 0) :
    Real.sqrt a > Real.sqrt b := by
  exact Real.sqrt_lt_sqrt h₂.le h₁

#print axioms solution
