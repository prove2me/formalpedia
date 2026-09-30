-- Prove2me | solution 2 for lean_workbook_plus_47985
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:18:21.949447+00:00
-- url     : https://prove2.me/submissions/1a13a81a-eb34-4c31-b767-f4964c00364b

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 0) :
  (a * b + b * c + c * a) ^ 2 = (1 / 4) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2   := by
  have h2 : c = -(a + b) := by linarith
  rw [h2]
  ring

#print axioms solution
