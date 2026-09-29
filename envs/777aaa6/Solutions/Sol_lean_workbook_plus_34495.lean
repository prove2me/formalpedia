-- Prove2me | solution 1 for lean_workbook_plus_34495
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:53.33771+00:00
-- url     : https://prove2.me/submissions/65175a81-e920-4932-8367-c25e41191103

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (2 + a + c) ^ 2 * (2 + b + d) ^ 2 ≥ 16 * (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have hpos_d : (0 : ℝ) ≤ d := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((2 + a + c) ^ 2 * (2 + b + d) ^ 2) - (16 * (1 + a) * (1 + b) * (1 + c) * (1 + d)) := by
    calc
      0 ≤ (4 : ℝ) * (1) * ((a + ((-1) * c)))^2 + (1 : ℝ) * (1) * (((a * b) + ((-1) * c * d)))^2 + (1 : ℝ) * (1) * (((a * d) + ((-1) * b * c)))^2 + (4 : ℝ) * (1) * ((b + ((-1) * d)))^2 + (4 : ℝ) * (d) * ((a + ((-1) * c)))^2 + (4 : ℝ) * (c) * ((b + ((-1) * d)))^2 + (4 : ℝ) * (b) * ((a + ((-1) * c)))^2 + (2 : ℝ) * ((b * d)) * ((a + ((-1) * c)))^2 + (4 : ℝ) * (a) * ((b + ((-1) * d)))^2 + (2 : ℝ) * ((a * c)) * ((b + ((-1) * d)))^2 := by positivity
      _ = ((2 + a + c) ^ 2 * (2 + b + d) ^ 2) - (16 * (1 + a) * (1 + b) * (1 + c) * (1 + d)) := by ring
  exact sub_nonneg.mp h
