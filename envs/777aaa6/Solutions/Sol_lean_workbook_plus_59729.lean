-- Prove2me | solution 1 for lean_workbook_plus_59729
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:20:08.667524+00:00
-- url     : https://prove2.me/submissions/01908b70-0e96-40df-a8df-e9fee727a5b0

import Mathlib

theorem solution : ∀ x : ℝ, abs x = Real.sqrt (x ^ 2) := by
  intro x
  exact (Real.sqrt_sq_eq_abs x).symm

#print axioms solution
