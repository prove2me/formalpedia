-- Prove2me | solution 1 for lean_workbook_plus_21750
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:44.475205+00:00
-- url     : https://prove2.me/submissions/a27cb530-6034-412e-86a0-2286f33e2a90

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 2 * b ^ 4 + a ^ 2 * (c + b) ^ 2 ≥ 2 * a * b * (a * c + b * c + b ^ 2) := by
  intros
  have h : (0 : ℝ) ≤ (2 * b ^ 4 + a ^ 2 * (c + b) ^ 2) - (2 * a * b * (a * c + b * c + b ^ 2)) := by
    calc
      0 ≤ (1 : ℝ) * (((b ^ 2) + ((-1) * a * c)))^2 + (1 : ℝ) * (((b ^ 2) + ((-1) * a * b)))^2 := by positivity
      _ = (2 * b ^ 4 + a ^ 2 * (c + b) ^ 2) - (2 * a * b * (a * c + b * c + b ^ 2)) := by ring
  exact sub_nonneg.mp h
