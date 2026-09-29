-- Prove2me | solution 1 for lean_workbook_plus_35537
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:58.756389+00:00
-- url     : https://prove2.me/submissions/8fbed1c0-4658-44c9-884e-2166d301cfd3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + 1) * (b + c + 1) * (c + a + 1) + 2 ≥ 7 * (a * b + b * c + a * c) + 2 * (a + b + c + a * b * c) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((a + b + 1) * (b + c + 1) * (c + a + 1) + 2) - (7 * (a * b + b * c + a * c) + 2 * (a + b + c + a * b * c)) := by
    calc
      0 ≤ (1 : ℝ) * (1) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (1) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * (1) * ((1 + ((-1) * c)))^2 + (1 : ℝ) * (c) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (c) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * (b) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (b) * ((1 + ((-1) * c)))^2 + (1 : ℝ) * (a) * ((1 + ((-1) * b)))^2 + (1 : ℝ) * (a) * ((1 + ((-1) * c)))^2 := by positivity
      _ = ((a + b + 1) * (b + c + 1) * (c + a + 1) + 2) - (7 * (a * b + b * c + a * c) + 2 * (a + b + c + a * b * c)) := by ring
  exact sub_nonneg.mp h
