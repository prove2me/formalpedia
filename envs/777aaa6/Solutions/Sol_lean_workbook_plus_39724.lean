-- Prove2me | solution 1 for lean_workbook_plus_39724
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:39:29.740746+00:00
-- url     : https://prove2.me/submissions/c6f2ff24-8df7-46a5-91e2-852e22a63596

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℕ) : Real.sqrt (a * b) ≤ (a + b) / 2   := by
  push_cast
  change Real.sqrt ((a : ℝ) * (b : ℝ)) ≤ ((a : ℝ) + (b : ℝ)) / 2
  apply (Real.sqrt_le_left (by positivity)).2
  nlinarith only [sq_nonneg ((a : ℝ) - (b : ℝ))]

#print axioms solution
