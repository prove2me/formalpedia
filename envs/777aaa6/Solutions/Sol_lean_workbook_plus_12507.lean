-- Prove2me | solution 1 for lean_workbook_plus_12507
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-10T15:15:04.345635+00:00
-- url     : https://prove2.me/submissions/56c10fd0-af8a-45d8-b542-a9434a67a48c

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) : b^2 + a^2 + 2 * a + 1 ≥ 2 * a * b + 2 * b := by
  nlinarith [sq_nonneg (b - a - 1)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b x y : ℝ) (h₁ : x + y = a) (h₂ : x * y = b) : b^2 + a^2 + 2 * a + 1 ≥ 2 * a * b + 2 * b   := by apply solution
