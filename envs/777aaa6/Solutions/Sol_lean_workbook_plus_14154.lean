-- Prove2me | solution 1 for lean_workbook_plus_14154
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:28.569936+00:00
-- url     : https://prove2.me/submissions/50e497a6-6321-4262-b7b8-1418c51683d2

import Mathlib
set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : ∃ Q : ℚ, b * Q > 1   := by
  obtain ⟨q, hq⟩ := exists_rat_gt (1 / b)
  use q
  rw [mul_comm]
  rw [div_lt_iff₀ hb] at hq
  assumption

#print axioms solution
