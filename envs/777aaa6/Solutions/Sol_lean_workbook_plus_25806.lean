-- Prove2me | solution 1 for lean_workbook_plus_25806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:46.778859+00:00
-- url     : https://prove2.me/submissions/a373933e-f231-4adb-ad34-b192c917396b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x^2 + 5*x + 6 = 0 ↔ x = -2 ∨ x = -3 := by
  have he : x^2+5*x+6 = (x+2)*(x+3) := by ring
  rw [he,mul_eq_zero]
  constructor
  · rintro (h|h)
    · left; linarith
    · right; linarith
  · rintro (rfl|rfl) <;> norm_num
