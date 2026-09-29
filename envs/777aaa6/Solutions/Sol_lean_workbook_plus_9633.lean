-- Prove2me | solution 1 for lean_workbook_plus_9633
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:03.646542+00:00
-- url     : https://prove2.me/submissions/aef843b7-f26b-49ff-95ec-cd9189b0566f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b) := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
