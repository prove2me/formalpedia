-- Prove2me | solution 1 for lean_workbook_plus_54319
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-10T15:01:47.351646+00:00
-- url     : https://prove2.me/submissions/bf41162f-0eed-499d-a307-78112a4dbbf1

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (a b: ℝ) : (a - b) ^ 2 ≥ 0 → a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  intro h
  nlinarith [sq_nonneg (a - b)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b: ℝ) : (a - b) ^ 2 ≥ 0 → a ^ 2 + b ^ 2 ≥ 2 * a * b   := by apply solution
