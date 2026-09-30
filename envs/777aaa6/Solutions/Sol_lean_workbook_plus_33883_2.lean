-- Prove2me | solution 2 for lean_workbook_plus_33883
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:36:02.178069+00:00
-- url     : https://prove2.me/submissions/d6a302b1-e0c0-4bb3-b289-42012897dd7c

import Mathlib
set_option autoImplicit false

theorem solution {a b c : ℤ} (h : a + b + c = 0) : a^5 + b^5 + c^5 = -5 * a * b * (a + b) * (a^2 + a * b + b^2)   := by
  have h1 : c = -(a + b) := by linarith
  rw [h1]
  ring

#print axioms solution
