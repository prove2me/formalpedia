-- Prove2me | solution 1 for lean_workbook_plus_63464
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:26.047973+00:00
-- url     : https://prove2.me/submissions/2c00766c-8c29-48de-a26d-8b7eff15e49d

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) : (c^2 - (a + b) * c + (a + b)^2 / 4) ≥ 0   := by
  simp [sq]
  nlinarith [sq_nonneg (c - (a + b) / 2)]

#print axioms solution
