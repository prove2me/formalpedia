-- Prove2me | solution 1 for lean_workbook_plus_19537
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:11.425551+00:00
-- url     : https://prove2.me/submissions/279c673a-d454-4432-be02-dc34adeaeb20

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2 ≥ 9 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (8 * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2) - (9 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) := by
    calc
      0 ≤ (8 : ℝ) * (1) * (((a ^ 3) + ((-1) * a * b * c)))^2 + (8 : ℝ) * (1) * ((((-1) * (b ^ 3)) + (a * b * c)))^2 + (8 : ℝ) * (1) * ((((-1) * (c ^ 3)) + (a * b * c)))^2 + (7 : ℝ) * ((b * c)) * (((a ^ 2) + ((-1) * b * c)))^2 + (7 : ℝ) * ((a * c)) * ((((-1) * (b ^ 2)) + (a * c)))^2 + (7 : ℝ) * ((a * b)) * ((((-1) * (c ^ 2)) + (a * b)))^2 := by positivity
      _ = (8 * (a ^ 3 + b ^ 3 + c ^ 3) ^ 2) - (9 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) := by ring
  exact sub_nonneg.mp h
