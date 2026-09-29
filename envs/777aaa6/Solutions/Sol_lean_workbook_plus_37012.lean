-- Prove2me | solution 1 for lean_workbook_plus_37012
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:12.110694+00:00
-- url     : https://prove2.me/submissions/f6c20c7e-d47f-46dc-94ca-01593c6f7bfa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, 1 ≤ a ∧ a ≤ 1 ∧ 1 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 1 → a * b + b * c + c * a + 1 ≥ 0 := by
  intro a b c
  intros
  nlinarith
