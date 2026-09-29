-- Prove2me | solution 1 for lean_workbook_plus_11075
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-10T16:01:08.165752+00:00
-- url     : https://prove2.me/submissions/5b239bd4-51be-4a8f-99c8-1ff1d17a57a8

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

theorem solution (a b c d : ℝ) : (2 * a - 2 * b + c) ^ 2 + (b - 2 * c + 2 * d) ^ 2 + (a - c + d) ^ 2 + (b - c) ^ 2 + (1 / 2) * (2 * a - b) ^ 2 + (1 / 2) * (b - 2 * d) ^ 2 ≥ 0 := by
  positivity

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b c d : ℝ) : (2 * a - 2 * b + c) ^ 2 + (b - 2 * c + 2 * d) ^ 2 + (a - c + d) ^ 2 + (b - c) ^ 2 + (1 / 2) * (2 * a - b) ^ 2 + (1 / 2) * (b - 2 * d) ^ 2 ≥ 0   := by apply solution
