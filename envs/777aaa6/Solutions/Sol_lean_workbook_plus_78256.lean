-- Prove2me | solution 1 for lean_workbook_plus_78256
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:02:09.471725+00:00
-- url     : https://prove2.me/submissions/01e522aa-5158-41d1-9a56-c20766285f91

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, (z - x) ^ 2 / 2 ≤ (y - x) ^ 2 + (z - y) ^ 2   := by
  intro x y z
  have h1 : 0 ≤ (y - x - (z - y)) ^ 2 := sq_nonneg _
  linarith

#print axioms solution
