-- Prove2me | solution 1 for lean_workbook_plus_61970
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:52:04.474719+00:00
-- url     : https://prove2.me/submissions/791ffca7-d8cc-4a73-aa9e-a6055bb9154e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ x : ℝ, 0 < x ∧ x ≤ 1 → x / (x + 1) ≥ x / 2 := by
  intro x hx
  exact div_le_div_of_nonneg_left (le_of_lt hx.1) (by linarith [hx.1]) (by linarith [hx.2])
