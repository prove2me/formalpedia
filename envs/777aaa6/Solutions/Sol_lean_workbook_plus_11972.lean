-- Prove2me | solution 1 for lean_workbook_plus_11972
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:47.157704+00:00
-- url     : https://prove2.me/submissions/44421d85-df15-45a4-b4b1-4dacd3c349e7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^3 * b + a * b^3 + a + b ≥ 2 * a * b + a^2 * b + a * b^2 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^3 * b + a * b^3 + a + b) - (2 * a * b + a^2 * b + a * b^2) := by
    calc
      0 ≤ (1 : ℝ) * (b) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (a) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * ((a * b)) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * ((a * b)) * ((1 + ((-1) * b)))^2 := by positivity
      _ = (a^3 * b + a * b^3 + a + b) - (2 * a * b + a^2 * b + a * b^2) := by ring
  exact sub_nonneg.mp h
