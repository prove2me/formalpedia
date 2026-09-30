-- Prove2me | solution 1 for lean_workbook_plus_11272
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:51:01.536434+00:00
-- url     : https://prove2.me/submissions/3b3a7536-bf36-49f1-80d7-8ed9665e989a

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (hab : a + b + c = 3) : a^2 + b^2 + a^2 * b^2 + a * b * c ≥ 4 * a * b   := by
  have hc : c = 3 - a - b := by linarith
  rw [hc]
  nlinarith [sq_nonneg (2 * a * b - a - b), sq_nonneg (a - b)]

#print axioms solution
