-- Prove2me | solution 1 for lean_workbook_plus_9565
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-04-10T18:17:51.73147+00:00
-- url     : https://prove2.me/submissions/276cc9a0-2b0e-4071-a6b6-dead23a652bc

import Theorems.Thm_lean_workbook_plus_9565
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

theorem solution (x : ℝ) : x^4 - x^2 - 2*x + 2 ≥ 0 := by
  have h : x^4 - x^2 - 2*x + 2 = (x - 1)^2 * ((x + 1)^2 + 1) := by ring
  rw [h]
  positivity
