-- Prove2me | solution 1 for lean_workbook_plus_64393
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:54:28.279644+00:00
-- url     : https://prove2.me/submissions/9e34845c-b7bb-4654-a228-775ddff0bacc

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 0) : (a^5 + b^5 + c^5) / 5 = (a^3 + b^3 + c^3) / 3 * (a^2 + b^2 + c^2) / 2   := by
  have h' : c = -(a + b) := by linarith
  rw [h']
  ring

#print axioms solution
