-- Prove2me | solution 1 for lean_workbook_plus_68898
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:16:23.319606+00:00
-- url     : https://prove2.me/submissions/f2f92183-3f87-4404-9dab-0bc66d106ae3

import Mathlib
set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (h : f (-1) = f (-1) ^ 2) : f (-1) = 0 ∨ f (-1) = 1   := by
  have hz : f (-1) * (f (-1) - 1) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp hz with hzero | hone
  · exact Or.inl hzero
  · right
    linarith

#print axioms solution
