-- Prove2me | solution 1 for lean_workbook_plus_71351
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:27.77754+00:00
-- url     : https://prove2.me/submissions/3f83f2cb-c4ad-47ed-a0d2-c17119da268a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b u v : ℝ} (ha : a > 0) (hb : b > 0) (hv : v > 0) (hab : a + b = 2 * u) (h : a * b = v ^ 2) : a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2)) - ((a + b) * (a * b - 1)) := by
    calc
      0 ≤ ((1 / 3) : ℝ) * (1) * (((b * (a ^ 2)) + ((-1) * a * b)))^2 + ((2 / 3) : ℝ) * (1) * (((b * (a ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((1 / 3) : ℝ) * (1) * (((a * b) + ((-1) * a * (b ^ 2))))^2 + ((1 / 3) : ℝ) * (b) * ((1 + ((-1) * a)))^2 + ((2 / 3) : ℝ) * (b) * ((1 + ((-1) * a * b)))^2 + ((2 / 3) : ℝ) * (a) * ((1 + ((-1) * a * b)))^2 + ((1 / 3) : ℝ) * (a) * ((1 + ((-1) * b)))^2 + ((4 / 3) : ℝ) * ((a * b)) * ((1 + ((-1) * a * b)))^2 := by positivity
      _ = (a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2)) - ((a + b) * (a * b - 1)) := by ring
  exact sub_nonneg.mp h
