-- Prove2me | solution 1 for lean_workbook_plus_9107
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:28.295278+00:00
-- url     : https://prove2.me/submissions/3c1c4ad6-0caf-411e-8d22-3a0bb1209e96

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y : ℝ, (x + y) ^ 4 - 8 * x * y * (x + y) ^ 2 + 16 * x ^ 2 * y ^ 2 ≥ 0 := by
  intro x y
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
