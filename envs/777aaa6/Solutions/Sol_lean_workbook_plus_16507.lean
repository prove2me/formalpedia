-- Prove2me | solution 1 for lean_workbook_plus_16507
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:24.950788+00:00
-- url     : https://prove2.me/submissions/1b9d6496-9927-4a20-aa52-76134d2f4571

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b : ℝ, 2 * (a ^ 2 + b ^ 2) ^ 2 ≥ (a ^ 2 + b ^ 2) * (a + b) ^ 2 := by
  intro a b
  intros
  have h : (0 : ℝ) ≤ (2 * (a ^ 2 + b ^ 2) ^ 2) - ((a ^ 2 + b ^ 2) * (a + b) ^ 2) := by
    calc
      0 ≤ (1 : ℝ) * (((b ^ 2) + ((-1) * a * b)))^2 + (1 : ℝ) * ((((-1) * (a ^ 2)) + (a * b)))^2 := by positivity
      _ = (2 * (a ^ 2 + b ^ 2) ^ 2) - ((a ^ 2 + b ^ 2) * (a + b) ^ 2) := by ring
  exact sub_nonneg.mp h
