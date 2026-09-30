-- Prove2me | solution 1 for lean_workbook_plus_61375
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:55:47.61144+00:00
-- url     : https://prove2.me/submissions/81fd8d89-4c09-44b7-9d7b-5b5bb3dfe596

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 0) : (a^2 + b^2 + c^2) / 2 * (a^5 + b^5 + c^5) / 5 = (a^7 + b^7 + c^7) / 7   := by
  have h1 : c = -(a+b) := by linarith
  rw [h1]
  ring

#print axioms solution
