-- Prove2me | solution 1 for lean_workbook_plus_36154
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:11.707631+00:00
-- url     : https://prove2.me/submissions/fa21a054-1645-4e82-866d-8032ce208516

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b c : ℝ, (a * b + a * c + b * c) ^ 2 ≥ 3 * a * b * c * (a + b + c) := by
  intro a b c
  intros
  have h : (0 : ℝ) ≤ ((a * b + a * c + b * c) ^ 2) - (3 * a * b * c * (a + b + c)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((b * c) + ((-1) * a * c)))^2 + ((1 / 2) : ℝ) * (((b * c) + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * (((a * c) + ((-1) * a * b)))^2 := by positivity
      _ = ((a * b + a * c + b * c) ^ 2) - (3 * a * b * c * (a + b + c)) := by ring
  exact sub_nonneg.mp h
