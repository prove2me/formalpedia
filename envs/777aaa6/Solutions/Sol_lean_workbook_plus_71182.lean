-- Prove2me | solution 1 for lean_workbook_plus_71182
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:58.162088+00:00
-- url     : https://prove2.me/submissions/9f48183c-3470-41e6-ac86-ac0035ca440c

import Mathlib

theorem solution (a b : ℝ) :
    b^2 * (1 + a^4) ≤ (b^4 + 1) / 2 * (1 + a^4) := by
  have h : 0 ≤ (b^2 - 1)^2 * (1 + a^4) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith

#print axioms solution
