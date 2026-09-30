-- Prove2me | solution 1 for lean_workbook_plus_16301
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:30.815669+00:00
-- url     : https://prove2.me/submissions/aca6cdba-c11c-408c-b1e4-1899b07b8ee9

import Mathlib
set_option autoImplicit false

theorem solution (a : ℕ → ℝ) : (a 1 + a 2 + a 3 + a 4) ^ 2 - 4 * (a 1 * a 2 + a 2 * a 3 + a 3 * a 4 + a 4 * a 1) ≥ 0   := by
  simp [add_comm]
  nlinarith [sq_nonneg (a 1 - a 2 + a 3 - a 4)]

#print axioms solution
