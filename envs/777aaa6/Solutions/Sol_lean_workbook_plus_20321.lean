-- Prove2me | solution 1 for lean_workbook_plus_20321
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:26.889603+00:00
-- url     : https://prove2.me/submissions/e285c5ff-66ba-47d9-9d0d-91fbfbb78610

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 5 ≥ 2 * a^2 + 2 * b^2 + 2 * c^2 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^3 + b^3 + c^3 + 5) - (2 * a^2 + 2 * b^2 + 2 * c^2) := by
    calc
      0 ≤ ((1 / 5) : ℝ) * (1) * (1)^2 + ((8 / 5) : ℝ) * (1) * ((1 + ((-1 / 2) * a)))^2 + ((8 / 5) : ℝ) * (1) * ((1 + ((-1 / 2) * b)))^2 + ((8 / 5) : ℝ) * (1) * ((1 + ((-1 / 2) * c)))^2 + ((4 / 5) : ℝ) * (c) * ((1 + ((-1) * c)))^2 + ((4 / 5) : ℝ) * (c) * ((1 + ((-1 / 2) * c)))^2 + ((4 / 5) : ℝ) * (b) * ((1 + ((-1) * b)))^2 + ((4 / 5) : ℝ) * (b) * ((1 + ((-1 / 2) * b)))^2 + ((4 / 5) : ℝ) * (a) * ((1 + ((-1) * a)))^2 + ((4 / 5) : ℝ) * (a) * ((1 + ((-1 / 2) * a)))^2 := by positivity
      _ = (a^3 + b^3 + c^3 + 5) - (2 * a^2 + 2 * b^2 + 2 * c^2) := by ring
  exact sub_nonneg.mp h
