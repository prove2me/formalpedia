-- Prove2me | solution 1 for lean_workbook_plus_35149
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:34.356711+00:00
-- url     : https://prove2.me/submissions/8d6b51ab-0702-4451-bdb6-9b6491e8d6d8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) * (a ^ 4 + b ^ 4) ≥ (a ^ 2 + b ^ 2) * (a ^ 3 + b ^ 3) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((a + b) * (a ^ 4 + b ^ 4)) - ((a ^ 2 + b ^ 2) * (a ^ 3 + b ^ 3)) := by
    calc
      0 ≤ (1 : ℝ) * (b) * (((a ^ 2) + ((-1) * a * b)))^2 + (1 : ℝ) * (a) * ((((-1) * (b ^ 2)) + (a * b)))^2 := by positivity
      _ = ((a + b) * (a ^ 4 + b ^ 4)) - ((a ^ 2 + b ^ 2) * (a ^ 3 + b ^ 3)) := by ring
  exact sub_nonneg.mp h
