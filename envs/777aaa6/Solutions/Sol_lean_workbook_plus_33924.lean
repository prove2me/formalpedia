-- Prove2me | solution 1 for lean_workbook_plus_33924
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:39.371211+00:00
-- url     : https://prove2.me/submissions/59ae50e7-861f-45d5-aa19-fbb14429470f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 3 + (2 * a + b) ^ 3 + (3 * a) ^ 3 ≤ 8 * (9 * a ^ 3 + b ^ 3) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (8 * (9 * a ^ 3 + b ^ 3)) - ((a + b) ^ 3 + (2 * a + b) ^ 3 + (3 * a) ^ 3) := by
    calc
      0 ≤ ((21 / 5) : ℝ) * (b) * ((a + ((-1) * b)))^2 + ((36 / 5) : ℝ) * (b) * ((a + ((-1 / 2) * b)))^2 + ((48 / 5) : ℝ) * (a) * (a)^2 + ((132 / 5) : ℝ) * (a) * ((a + ((-1 / 2) * b)))^2 := by positivity
      _ = (8 * (9 * a ^ 3 + b ^ 3)) - ((a + b) ^ 3 + (2 * a + b) ^ 3 + (3 * a) ^ 3) := by ring
  exact sub_nonneg.mp h
