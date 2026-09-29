-- Prove2me | solution 1 for lean_workbook_plus_73986
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:29.573583+00:00
-- url     : https://prove2.me/submissions/4ff18451-c017-4da7-9b78-21fe3d784b45

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b : ℝ, a > 0 ∧ b > 0 → 8 * (a ^ 4 + b ^ 4) ≥ (a + b) ^ 4 := by
  intro a b
  intros
  nlinarith [sq_nonneg (a * b), sq_nonneg (a^2 - b^2)]
