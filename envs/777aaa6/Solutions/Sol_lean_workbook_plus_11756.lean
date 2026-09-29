-- Prove2me | solution 1 for lean_workbook_plus_11756
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:42:29.364757+00:00
-- url     : https://prove2.me/submissions/8f9af460-0280-42ea-8eca-425456289292

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, 2 * Real.sqrt (1 + 2 * (x - 3) ^ 2) * Real.sqrt ((x - 2) ^ 2 + 1) ≥ -3 * x ^ 2 + 16 * x - 87 / 4 := by
  intro x
  have hL : 0 ≤ 2 * Real.sqrt (1+2*(x-3)^2) * Real.sqrt ((x-2)^2+1) := by positivity
  nlinarith [sq_nonneg (3*x-8)]
