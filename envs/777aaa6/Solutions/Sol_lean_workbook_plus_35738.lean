-- Prove2me | solution 1 for lean_workbook_plus_35738
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:44.369243+00:00
-- url     : https://prove2.me/submissions/0ca4f272-5292-4398-90cf-dce7dac6547b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 * b^2 + b^3 * c^2 + c^3 * a^2 ≥ a^2 * b^2 * c + a * b^2 * c^2 + a^2 * b * c^2 := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^3 * b^2 + b^3 * c^2 + c^3 * a^2) - (a^2 * b^2 * c + a * b^2 * c^2 + a^2 * b * c^2) := by
    calc
      0 ≤ (1 : ℝ) * (c) * (((a * b) + ((-1) * a * c)))^2 + (1 : ℝ) * (b) * (((a * c) + ((-1) * b * c)))^2 + (1 : ℝ) * (a) * (((a * b) + ((-1) * b * c)))^2 := by positivity
      _ = (a^3 * b^2 + b^3 * c^2 + c^3 * a^2) - (a^2 * b^2 * c + a * b^2 * c^2 + a^2 * b * c^2) := by ring
  exact sub_nonneg.mp h
