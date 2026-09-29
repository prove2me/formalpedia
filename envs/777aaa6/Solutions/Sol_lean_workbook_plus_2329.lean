-- Prove2me | solution 1 for lean_workbook_plus_2329
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-03-10T15:23:17.381505+00:00
-- url     : https://prove2.me/submissions/89ff941f-6986-4d31-b26f-048c06a49add

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

theorem solution (a : ℝ) : (a^3 - a + 2)^2 > 4 * a^2 * (a^2 + 1) * (a - 2) := by
  nlinarith [sq_nonneg (a^3 - 2*a^2 + 1), sq_nonneg (a^2 - a), sq_nonneg a, sq_nonneg (a - 1), sq_nonneg (a^2 - 2*a + 2)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a : ℝ) : (a^3 - a + 2)^2 > 4 * a^2 * (a^2 + 1) * (a - 2)   := by apply solution
