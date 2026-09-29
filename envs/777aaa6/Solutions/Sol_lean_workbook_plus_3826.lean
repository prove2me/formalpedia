-- Prove2me | solution 1 for lean_workbook_plus_3826
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-03-11T17:31:23.507861+00:00
-- url     : https://prove2.me/submissions/5c2324d5-2534-499f-aef9-706d306d0129

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution : ∀ u v w : ℝ, (2 * u - v - w) ^ 2 / 4 + 3 * (v - w) ^ 2 / 4 ≥ 0 := by
  intro u v w
  have h1 : (2 * u - v - w) ^ 2 ≥ 0 := sq_nonneg _
  have h2 : (v - w) ^ 2 ≥ 0 := sq_nonneg _
  nlinarith

-- Auto-generated type check: solution must match the target
theorem _type_check_target : ∀ u v w : ℝ, (2 * u - v - w) ^ 2 / 4 + 3 * (v - w) ^ 2 / 4 ≥ 0   := by apply solution
