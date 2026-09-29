-- Prove2me | solution 1 for lean_workbook_plus_66067
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:44:45.434212+00:00
-- url     : https://prove2.me/submissions/9b4a3bc2-7ca9-4e6c-85e6-fb16f67ee213

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (b c : ℝ) (hb : b ≥ 0) (hc : c ≥ 0): b^3 + c^3 + 8 - 6 * b * c ≥ 0 := by
  intros
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (b^3 + c^3 + 8 - 6 * b * c) - (0) := by
    calc
      0 ≤ (8 : ℝ) * (1) * ((1 + ((-1 / 2) * c)))^2 + (6 : ℝ) * (c) * ((1 + ((-1 / 2) * b)))^2 + (2 : ℝ) * (c) * ((1 + ((-1 / 2) * c)))^2 + ((1 / 2) : ℝ) * (c) * ((b + ((-1) * c)))^2 + (1 : ℝ) * (b) * ((b + ((-1) * c)))^2 := by positivity
      _ = (b^3 + c^3 + 8 - 6 * b * c) - (0) := by ring
  exact sub_nonneg.mp h
