-- Prove2me | solution 1 for lean_workbook_plus_22638
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:58:14.184985+00:00
-- url     : https://prove2.me/submissions/9c6dcde6-6e2f-40fc-a881-f8225669e484

import Mathlib
set_option autoImplicit false

theorem solution (K : ℝ) : (36 * K) ^ 2 - 4 * 52 * (6 * K ^ 2 + 3) ≥ 0 ↔ |K| ≥ Real.sqrt 13   := by
  change 0 <= (36 * K)^2 - 4 * 52 * (6 * K^2 + 3) <-> Real.sqrt 13 <= |K|
  rw [Real.sqrt_le_left (abs_nonneg K), sq_abs]
  constructor <;> intro h <;> nlinarith only [h]

#print axioms solution
