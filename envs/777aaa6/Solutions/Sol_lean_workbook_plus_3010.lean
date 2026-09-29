-- Prove2me | solution 1 for lean_workbook_plus_3010
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:40:55.469746+00:00
-- url     : https://prove2.me/submissions/482338b7-46eb-45b8-b00e-f1e806c8ec28

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a + b + c = 3 → Real.sqrt 3 ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  intro a b c
  intros
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
