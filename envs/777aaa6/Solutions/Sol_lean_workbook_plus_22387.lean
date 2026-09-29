-- Prove2me | solution 1 for lean_workbook_plus_22387
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:14:53.609546+00:00
-- url     : https://prove2.me/submissions/561b88b6-5550-42bc-ad25-77b40ac2873c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b c : ℝ) : (3 * (a * b + b * c + c * a)) / (a + b + c) ^ 2 ≤ 1 := by
  by_cases hzero : a+b+c = 0
  · simp [hzero]
  have hp : 0 < (a+b+c)^2 := sq_pos_of_ne_zero hzero
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]
