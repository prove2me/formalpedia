-- Prove2me | solution 1 for lean_workbook_plus_69149
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:18:07.836346+00:00
-- url     : https://prove2.me/submissions/dd0436af-2ac0-4686-896a-84952a2596f4

import Mathlib
set_option autoImplicit false

theorem solution (y : ℝ) (k : ℝ) (hy: y ∈ Set.Icc 0 (4 * k - 1 / 2)) : 1 / 8 + y / 4 ∈ Set.Icc 0 k   := by
  simp only [Set.mem_Icc] at hy ⊢
  constructor
  linarith
  linarith [hy.2]

#print axioms solution
