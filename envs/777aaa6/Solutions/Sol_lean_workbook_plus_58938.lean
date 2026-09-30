-- Prove2me | solution 1 for lean_workbook_plus_58938
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:38:20.115412+00:00
-- url     : https://prove2.me/submissions/b52ada65-2f98-4b33-9691-4b865535c80a

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : ((x^2 - 1 / 2)^2 + (x - 1 / 2)^2) > 0   := by
  by_contra h
  have hsum : (x^2 - 1 / 2)^2 + (x - 1 / 2)^2 ≤ 0 := le_of_not_gt h
  have hfirst : (x^2 - 1 / 2)^2 = 0 :=
    le_antisymm (by linarith [sq_nonneg (x - 1 / 2)]) (sq_nonneg _)
  have hsecond : (x - 1 / 2)^2 = 0 :=
    le_antisymm (by linarith [sq_nonneg (x^2 - 1 / 2)]) (sq_nonneg _)
  have hx : x = 1 / 2 := by
    have hz := sq_eq_zero_iff.mp hsecond
    linarith only [hz]
  rw [hx] at hfirst
  norm_num at hfirst

#print axioms solution
