-- Prove2me | solution 1 for lean_workbook_plus_19627
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-04-10T18:17:52.12642+00:00
-- url     : https://prove2.me/submissions/d6e5a117-95f5-437e-8a3c-46664cca26c8

import Theorems.Thm_lean_workbook_plus_19627
import Mathlib.Tactic.Positivity

theorem solution (a b : ℝ) : (a - b) ^ 2 / 4 + 3 * ((a + b) / 2 - 1) ^ 2 ≥ 0 := by
  positivity
