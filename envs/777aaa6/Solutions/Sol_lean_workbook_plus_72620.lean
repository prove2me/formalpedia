-- Prove2me | solution 1 for lean_workbook_plus_72620
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:36:05.866451+00:00
-- url     : https://prove2.me/submissions/bbf68d49-a9db-488f-b909-fde9b56b444c

import Mathlib

set_option autoImplicit false

theorem solution (x : ℝ) : x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = 0 ↔
    x = 1 ∨ x = 2 ∨ x = 3 := by
  have hf : x ^ 3 - 6 * x ^ 2 + 11 * x - 6 = (x - 1) * (x - 2) * (x - 3) := by ring
  rw [hf]
  simp [mul_eq_zero, sub_eq_zero, or_assoc]
