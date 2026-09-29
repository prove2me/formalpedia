-- Prove2me | solution 1 for lean_workbook_plus_35525
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:14.746423+00:00
-- url     : https://prove2.me/submissions/3fbe6b02-645d-4e85-b9bc-f6a5da3dd44b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (k : ℝ) (a : ℝ) (h : k ≥ 0) : (k + 2) * (1 + a ^ 2 + k * a ^ 4) ≥ (1 + a + k * a ^ 2) ^ 2 := by
  intros
  have hpos_k : (0 : ℝ) ≤ k := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((k + 2) * (1 + a ^ 2 + k * a ^ 4)) - ((1 + a + k * a ^ 2) ^ 2) := by
    calc
      0 ≤ (1 : ℝ) * (1) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (k) * ((1 + ((-1) * (a ^ 2))))^2 + (1 : ℝ) * (k) * ((a + ((-1) * (a ^ 2))))^2 := by positivity
      _ = ((k + 2) * (1 + a ^ 2 + k * a ^ 4)) - ((1 + a + k * a ^ 2) ^ 2) := by ring
  exact sub_nonneg.mp h
