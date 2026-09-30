-- Prove2me | solution 1 for lean_workbook_plus_37513
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:08.718492+00:00
-- url     : https://prove2.me/submissions/41417528-13cf-47c9-acfa-9d4b8ab52a5e

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y z : ℝ, 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2   := by
  intro x y z
  linarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]

#print axioms solution
