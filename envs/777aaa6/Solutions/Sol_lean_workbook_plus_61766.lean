-- Prove2me | solution 1 for lean_workbook_plus_61766
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:53:14.278979+00:00
-- url     : https://prove2.me/submissions/d99f5b10-4b69-45d7-98af-343506eb50b9

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x : ℝ, (1 - x ^ 2) + (1 - x) ^ 2 / 4 ≤ 4 / 3   := by
  intro x
  nlinarith only [sq_nonneg (3 * x + 1)]

#print axioms solution
