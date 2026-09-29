-- Prove2me | solution 1 for lean_workbook_plus_39772
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:10.077018+00:00
-- url     : https://prove2.me/submissions/dc0f6657-fa52-4bf6-806c-c327144f514e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y : ℝ, y ≥ 0 ∧ y * (y + 1) ≤ (x + 1) ^ 2 → y * (y - 1) ≤ x ^ 2 := by
  intro x y
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
