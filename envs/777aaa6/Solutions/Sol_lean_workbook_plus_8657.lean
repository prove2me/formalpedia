-- Prove2me | solution 1 for lean_workbook_plus_8657
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:54.418279+00:00
-- url     : https://prove2.me/submissions/721f6f96-a6b5-47d4-af2c-6cbc8c36f7e8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ≥ a^2 * b^2 * c + b^2 * c^2 * a + c^2 * a^2 * b := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^3 * b^2 + b^3 * c^2 + c^3 * a^2) - (a^2 * b^2 * c + b^2 * c^2 * a + c^2 * a^2 * b) := by
    calc
      0 ≤ (1 : ℝ) * (c) * (((a * b) + ((-1) * a * c)))^2 + (1 : ℝ) * (b) * (((a * c) + ((-1) * b * c)))^2 + (1 : ℝ) * (a) * (((a * b) + ((-1) * b * c)))^2 := by positivity
      _ = (a^3 * b^2 + b^3 * c^2 + c^3 * a^2) - (a^2 * b^2 * c + b^2 * c^2 * a + c^2 * a^2 * b) := by ring
  exact sub_nonneg.mp h
