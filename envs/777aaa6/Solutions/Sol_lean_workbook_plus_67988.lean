-- Prove2me | solution 1 for lean_workbook_plus_67988
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:24.447527+00:00
-- url     : https://prove2.me/submissions/1cf0e0f0-ac10-437b-bb64-9a5c6ea73bd2

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℂ) (hab : a + b + c = 0) : 2 * (a^5 + b^5 + c^5) = 5 * a * b * c * (a^2 + b^2 + c^2)   := by
  have : c = -(a + b) := by linear_combination hab
  rw [this]
  ring

#print axioms solution
