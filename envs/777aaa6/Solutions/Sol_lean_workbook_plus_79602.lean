-- Prove2me | solution 1 for lean_workbook_plus_79602
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-03-03T22:12:58.197663+00:00
-- url     : https://prove2.me/submissions/2be4ebcb-c857-42db-8306-a6730343783c

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) : a^2 + b^2 - 2*a*b ≥ 0 := by
  nlinarith [sq_nonneg (a - b)]

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b : ℝ) : a^2 + b^2 - 2*a*b ≥ 0   := by apply solution
