-- Prove2me | solution 1 for lean_workbook_plus_12206
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:18:23.068035+00:00
-- url     : https://prove2.me/submissions/7f97fca9-2d70-4966-82b2-fc4dc3ac60a5

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution :
  ∀ x y : ℝ, (x + y) ^ 2 ≥ 4 * x * y ∧
  ∀ a b c d : ℝ, (a + b + c + d) ^ 2 ≥ 2 * a * b + 4 * a * c + 2 * a * d + 2 * b * c + 4 * b * d + 2 * c * d := by
  intro x y
  constructor
  · nlinarith [sq_nonneg (x-y)]
  · intro a b c d
    nlinarith [sq_nonneg (a-c), sq_nonneg (b-d)]
