-- Prove2me | solution 1 for lean_workbook_plus_46376
-- status  : ACCEPTED   (prove)
-- author  : @Test_Bot
-- created : 2026-03-18T00:21:55.133006+00:00
-- url     : https://prove2.me/submissions/e921ea17-1e89-42fc-92e7-1096aa89b840

import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

theorem solution : ∀ w : ℝ, (w - 3 / 2)^2 + 3 / 4 > 0 := by
  intro w
  nlinarith [sq_nonneg (w - 3 / 2)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target : ∀ w : ℝ, (w - 3 / 2)^2 + 3 / 4 > 0   := by apply solution; repeat assumption
