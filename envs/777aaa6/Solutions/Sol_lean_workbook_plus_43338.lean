-- Prove2me | solution 1 for lean_workbook_plus_43338
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:16.714157+00:00
-- url     : https://prove2.me/submissions/fcbff437-292d-4246-913d-6ebdbec8612d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b : ℝ, 2 * (a ^ 2 + b ^ 2) ^ 2 ≥ (a ^ 2 - b ^ 2) ^ 2 := by
  intro a b
  intros
  nlinarith
