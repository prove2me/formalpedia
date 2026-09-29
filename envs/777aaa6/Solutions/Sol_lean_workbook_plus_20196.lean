-- Prove2me | solution 1 for lean_workbook_plus_20196
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:57.347351+00:00
-- url     : https://prove2.me/submissions/91198e5e-c289-4af5-82b8-e469fceb87c5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (hab : a + b + c = 0) : (a * b) ^ 2 + (b * c) ^ 2 + (a * c) ^ 2 + 6 * a * b * c ≥ -3 := by
  have hc : c=-a-b := by linarith
  rw [hc]
  nlinarith only [sq_nonneg (a^2+a*b-b-1),sq_nonneg (b^2+a*b-a-1),sq_nonneg ((a-1)*(b-1))]
