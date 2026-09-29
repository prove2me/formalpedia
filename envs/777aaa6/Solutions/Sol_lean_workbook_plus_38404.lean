-- Prove2me | solution 1 for lean_workbook_plus_38404
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:13.858925+00:00
-- url     : https://prove2.me/submissions/cccc7ee8-000e-4237-bc82-e900a1db29a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ ((a + b + c) ^ 2) - (3 * (a * b + b * c + c * a)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((c + ((-1) * b)))^2 + ((1 / 2) : ℝ) * ((c + ((-1) * a)))^2 + ((1 / 2) : ℝ) * ((b + ((-1) * a)))^2 := by positivity
      _ = ((a + b + c) ^ 2) - (3 * (a * b + b * c + c * a)) := by ring
  exact sub_nonneg.mp h
