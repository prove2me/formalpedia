-- Prove2me | solution 1 for lean_workbook_plus_30307
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:28.289714+00:00
-- url     : https://prove2.me/submissions/fe996bfc-f747-40a3-9d5d-cde3ad5d696c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b : ℝ, a > 0 ∧ b > 0 → a * b * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1) := by
  intro a b
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a * b * (a ^ 2 + b ^ 2 - 2)) - ((a + b) * (a * b - 1)) := by
    calc
      0 ≤ (1 : ℝ) * (b) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (a) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * ((a * b)) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * ((a * b)) * ((1 + ((-1) * b)))^2 := by positivity
      _ = (a * b * (a ^ 2 + b ^ 2 - 2)) - ((a + b) * (a * b - 1)) := by ring
  exact sub_nonneg.mp h
