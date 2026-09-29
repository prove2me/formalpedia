-- Prove2me | solution 1 for lean_workbook_plus_4323
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-04-10T14:20:20.592518+00:00
-- url     : https://prove2.me/submissions/cdec90aa-a68b-45e5-a668-180c79a738d5

import Theorems.Thm_lean_workbook_plus_4323
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (a b : ℝ) : 4 * b ^ 2 * (a ^ 2 + b ^ 2 - 2 * a * b) ≥ 0 := by
  have h : a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 := by ring
  rw [h]
  positivity
