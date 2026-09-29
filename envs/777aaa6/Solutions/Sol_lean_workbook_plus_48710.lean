-- Prove2me | solution 1 for lean_workbook_plus_48710
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:09:28.63755+00:00
-- url     : https://prove2.me/submissions/ea7c2cf9-771f-4ff7-a927-ecbaf3762747

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a ^ 4 + b ^ 4 + c ^ 4 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a ^ 3 * b + a * b ^ 3 + b ^ 3 * c + b * c ^ 3 + c ^ 3 * a + c * a ^ 3 := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
