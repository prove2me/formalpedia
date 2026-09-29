-- Prove2me | solution 1 for lean_workbook_plus_49617
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:15.898481+00:00
-- url     : https://prove2.me/submissions/47069d08-ecbb-4823-98a9-ea0621484e11

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h : c = 0) : 2 + (1 / 4) * ((a - b) ^ 2 + a ^ 2 + b ^ 2) ≥ a + b := by
  intros
  have h : (0 : ℝ) ≤ (2 + (1 / 4) * ((a - b) ^ 2 + a ^ 2 + b ^ 2)) - (a + b) := by
    calc
      0 ≤ (1 : ℝ) * ((1 + ((-1 / 2) * b)))^2 + (1 : ℝ) * ((1 + ((-1 / 2) * a)))^2 + ((1 / 4) : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = (2 + (1 / 4) * ((a - b) ^ 2 + a ^ 2 + b ^ 2)) - (a + b) := by ring
  exact sub_nonneg.mp h
