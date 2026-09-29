-- Prove2me | solution 1 for lean_workbook_plus_5763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:17.430586+00:00
-- url     : https://prove2.me/submissions/eca5747b-a49d-403f-8abd-fbeb682fb09a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 * b^2 * (a^2 + b^2 - 2) ≥ (a + b) * (a * b - 1) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a^2 * b^2 * (a^2 + b^2 - 2)) - ((a + b) * (a * b - 1)) := by
    calc
      0 ≤ ((1 / 3) : ℝ) * (1) * (((b * (a ^ 2)) + ((-1) * a * b)))^2 + ((2 / 3) : ℝ) * (1) * (((b * (a ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((1 / 3) : ℝ) * (1) * (((a * b) + ((-1) * a * (b ^ 2))))^2 + ((1 / 3) : ℝ) * (b) * ((1 + ((-1) * a)))^2 + ((2 / 3) : ℝ) * (b) * ((1 + ((-1) * a * b)))^2 + ((2 / 3) : ℝ) * (a) * ((1 + ((-1) * a * b)))^2 + ((1 / 3) : ℝ) * (a) * ((1 + ((-1) * b)))^2 + ((4 / 3) : ℝ) * ((a * b)) * ((1 + ((-1) * a * b)))^2 := by positivity
      _ = (a^2 * b^2 * (a^2 + b^2 - 2)) - ((a + b) * (a * b - 1)) := by ring
  exact sub_nonneg.mp h
