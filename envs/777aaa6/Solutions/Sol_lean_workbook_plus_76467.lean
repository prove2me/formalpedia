-- Prove2me | solution 1 for lean_workbook_plus_76467
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:41:17.854429+00:00
-- url     : https://prove2.me/submissions/99b57b66-cf2e-4929-be0a-5fbd61840840

import Mathlib

theorem solution : ∀ a b c : ℝ, a + b + c = 0 →
    a ^ 2 + b ^ 2 + c ^ 2 = 2 * a ^ 2 + 2 * a * b + 2 * b ^ 2 := by
  intro a b c h
  have hc : c = -(a + b) := by linarith
  rw [hc]
  ring
