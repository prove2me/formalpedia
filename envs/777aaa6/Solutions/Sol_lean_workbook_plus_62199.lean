-- Prove2me | solution 1 for lean_workbook_plus_62199
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-18T00:21:52.616556+00:00
-- url     : https://prove2.me/submissions/63d6197b-c0a1-4d92-ba20-5cabe6f4d97e

import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

theorem solution (x y : ℝ) : (x - y) ^ 2 ≥ 0 := by positivity

-- Auto-generated type check: solution must match the target
theorem _type_check_target (x y : ℝ) : (x - y) ^ 2 ≥ 0   := by apply solution; repeat assumption
