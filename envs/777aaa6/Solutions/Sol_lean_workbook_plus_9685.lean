-- Prove2me | solution 1 for lean_workbook_plus_9685
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:36.839575+00:00
-- url     : https://prove2.me/submissions/8e659a37-e910-44c4-8a9b-fee67558b35a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ p q : ℝ, p > 0 ∧ q > 0 → 25 + 6 * (Real.sqrt (p / q) - Real.sqrt (q / p)) ^ 2 ≥ 25 := by
  intro p q
  intros
  nlinarith
