-- Prove2me | solution 1 for lean_workbook_plus_53862
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-28T19:18:23.601703+00:00
-- url     : https://prove2.me/submissions/e2751dd8-5fea-467c-8d54-b75d9ef31561

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

theorem solution (a : ℝ) : a * ((a ^ 2 - 1) ^ 2 + a ^ 2) = 2 → a > 0 := by
  intro h
  by_contra hle
  push_neg at hle
  have h1 : (a ^ 2 - 1) ^ 2 + a ^ 2 ≥ 0 := by positivity
  nlinarith [sq_nonneg a, sq_nonneg (a ^ 2 - 1)]

-- Auto-generated: theorem statement as a def
def _final_theorem := ∀ (a : ℝ), a * ((a ^ 2 - 1) ^ 2 + a ^ 2) = 2 → a > 0

-- Auto-generated type check: solution must match the target
theorem _type_check_target : _final_theorem := solution
