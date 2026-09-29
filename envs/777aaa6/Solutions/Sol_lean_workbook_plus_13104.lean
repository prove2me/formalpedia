-- Prove2me | solution 1 for lean_workbook_plus_13104
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:36.889153+00:00
-- url     : https://prove2.me/submissions/754d5420-2195-4c81-a905-3a97495386c7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + 9 ≥ 6 * (a + b + c) := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ (3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + 9) - (6 * (a + b + c)) := by
    calc
      0 ≤ (3 : ℝ) * ((1 + ((-1) * c)))^2 + (3 : ℝ) * ((1 + ((-1) * b)))^2 + (3 : ℝ) * ((1 + ((-1) * a)))^2 := by positivity
      _ = (3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 + 9) - (6 * (a + b + c)) := by ring
  exact sub_nonneg.mp h
