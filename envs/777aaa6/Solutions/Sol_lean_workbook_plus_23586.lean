-- Prove2me | solution 1 for lean_workbook_plus_23586
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:27:53.061+00:00
-- url     : https://prove2.me/submissions/3c1a31c8-5f35-4863-af19-0d6768af2d3a

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a / (a + c - b) ≥ 0) :
  a / (a + c - b) + 1 ≥ 2 * Real.sqrt (a / (a + c - b))   := by
  have h2 : 0 ≤ (Real.sqrt (a / (a + c - b)) - 1) ^ 2 := sq_nonneg (Real.sqrt (a / (a + c - b)) - 1)
  rw [sub_sq] at h2
  have h3 : 0 ≤ a / (a + c - b) := by positivity
  rw [Real.sq_sqrt h3] at h2
  linarith [h, h2, h3]

#print axioms solution
