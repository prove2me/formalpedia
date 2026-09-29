-- Prove2me | solution 1 for lean_workbook_plus_1602
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:26:07.209791+00:00
-- url     : https://prove2.me/submissions/5b95eec9-d1f8-4784-a3d3-47936949b1f6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 → x^2 - x + 2 ≤ 2 := by
  intro x
  intros
  nlinarith
