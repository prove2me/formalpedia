-- Prove2me | solution 1 for lean_workbook_plus_75
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:50.443593+00:00
-- url     : https://prove2.me/submissions/e85b261a-7b0f-40d6-861f-a3b6f2f49b9d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c ≥ (a * b + b * c + c * a) * (a + b + c) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c) - ((a * b + b * c + c * a) * (a + b + c)) := by
    calc
      0 ≤ (1 : ℝ) * (c) * ((a + ((-1) * c)))^2 + (1 : ℝ) * (c) * ((b + ((-1) * c)))^2 + (1 : ℝ) * (b) * ((a + ((-1) * b)))^2 + (1 : ℝ) * (b) * ((b + ((-1) * c)))^2 + (1 : ℝ) * (a) * ((a + ((-1) * b)))^2 + (1 : ℝ) * (a) * ((a + ((-1) * c)))^2 := by positivity
      _ = (2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c) - ((a * b + b * c + c * a) * (a + b + c)) := by ring
  exact sub_nonneg.mp h
