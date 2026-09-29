-- Prove2me | solution 1 for lean_workbook_plus_50269
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:18.423298+00:00
-- url     : https://prove2.me/submissions/cbb5c8d1-d1ef-405f-a8c2-ae5d417376c8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ b c : ℝ, b^2 - b*c + c^2 ≥ (b + c)^2 / 4 := by
  intro b c
  intros
  nlinarith [sq_nonneg b, sq_nonneg c, sq_nonneg (b - c)]
