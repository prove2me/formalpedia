-- Prove2me | solution 1 for lean_workbook_plus_54662
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-15T15:09:08.784797+00:00
-- url     : https://prove2.me/submissions/0a451298-8550-49ee-8e2c-09b9ec006075

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution : ∀ x : ℝ, (x^2 - 3*x + 3/2)^2 - 2.25 + 3 ≥ 0 := by
  intro x
  -- (x² - 3x + 3/2)² + 0.75 ≥ 0, trivially true since square ≥ 0
  nlinarith [sq_nonneg (x^2 - 3*x + 3/2)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target : ∀ x : ℝ, (x^2 - 3*x + 3/2)^2 - 2.25 + 3 ≥ 0   := by apply solution; repeat assumption
