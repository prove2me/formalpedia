-- Prove2me | solution 1 for lean_workbook_plus_62136
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:59.750392+00:00
-- url     : https://prove2.me/submissions/8a514cec-3b9b-438d-b078-30f77a111a7a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (m M : ℝ) (x : ℝ) (g : ℝ → ℝ): m ≤ g (1 - x^2) ∧ g (1 - x^2) ≤ M ↔ m/4 ≤ (1/4) * g (1 - x^2) ∧ (1/4) * g (1 - x^2) ≤ M/4 := by
  intros
  grind
