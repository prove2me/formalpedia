-- Prove2me | solution 1 for lean_workbook_plus_57250
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:37.540774+00:00
-- url     : https://prove2.me/submissions/5762c561-188b-4f2d-addb-368b207668ed

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a ≤ (4:ℝ) / 3, (3 * a - 4) * (3 * a - 1) ^ 2 / (50 * (1 + a ^ 2)) ≤ 0   := by
  intro a ha
  apply div_nonpos_of_nonpos_of_nonneg
  apply mul_nonpos_of_nonpos_of_nonneg
  linarith
  nlinarith
  nlinarith

#print axioms solution
